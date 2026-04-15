# An Isabelle/HOL Formalisation of Archimedes' Cattle Problem

This is a formalisation of the solution to Archimedes' famous [‘cattle problem’](https://en.wikipedia.org/wiki/Archimedes%27s_cattle_problem) in Isabelle/HOL.

The development requires [Isabelle/2025-2](https://isabelle.in.tum.de/) and the corresponding version of the [Archive of Formal Proofs](https://isa-afp.org/). It builds on existing AFP entries on continued fractions and Pell's equation.

The development can be built by running `isabelle build -o document=pdf -P : -D .` from this directory.

The smallest non-trivial solution in decimal notation (consisting of 206545 digits) can be found in the file `solution`. This solution was computed in Isabelle using Isabelle's code generator.
