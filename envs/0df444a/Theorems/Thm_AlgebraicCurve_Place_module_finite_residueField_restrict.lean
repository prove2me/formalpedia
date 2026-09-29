-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_module_finite_residueField_restrict
-- name    : AlgebraicCurve.Place.module_finite_residueField_restrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/8ff123d4-e6a4-55a8-8f8d-5c8c40cedc55
-- title:
--   Residue degree of a place under a finite extension is finite
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, the two structure maps on $F'$ being compatible with that on $F$ (a scalar tower $K \to F \to F'$), and suppose $F'$ is finite-dimensional over $F$. Let $w$ be a place of $F'$ over $K$ in the sense of the project, that is: a valuation subring $\mathcal{O}_w \subseteq F'$ which contains the image of $K$ under the structure map, is not all of $F'$, and is a principal ideal ring. Its restriction $w.\text{restrict}\,F$ is the place of $F$ over $K$ whose valuation subring is the preimage $\mathcal{O}_w \cap F$ of $\mathcal{O}_w$ under the structure map $F \to F'$ (the three conditions being inherited). Writing $\mathrm{ResidueField}$ for the residue field of the local ring given by the valuation subring, the assertion is that $w.\mathrm{ResidueField} = \mathcal{O}_w/\mathfrak{m}_w$ is a finite module over $(w.\text{restrict}\,F).\mathrm{ResidueField} = (\mathcal{O}_w \cap F)/(\mathfrak{m}_w \cap F)$, for the algebra structure induced by the inclusion of valuation rings; that is, the residue degree $f(w\mid w|_F)$ is finite.
--
--   This is the finiteness half of the fundamental inequality $f(w \mid v) \le [F' : F]$ for a place $w$ of a finite extension $F'/F$ and its restriction $v = w|_F$. It feeds the divisor formalism for curves, being used in the computation of pushforwards of divisors over an algebraically closed base field and in the comparison of divisorial Weil pairings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_module_finite_residueField_restrict.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.module_finite_residueField_restrict (K F F' : Type*)
    [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] (w : Place K F') :
    Module.Finite (w.restrict F).ResidueField w.ResidueField := by sorry
