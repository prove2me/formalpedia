-- Prove2me | Theorems.Thm_Algebra_norm_prod
-- name    : Algebra.norm_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/c99c1e4b-261e-52f9-a0dd-5bb4c07ca4eb
-- title:
--   Norm of a product algebra is the product of norms
-- statement:
--   Let $R$ be a commutative ring and let $A$ and $B$ be rings equipped with $R$-algebra structures, each of which is free and finite as an $R$-module. Let $x = (x_1, x_2)$ be an element of the product algebra $A \times B$ (with its componentwise $R$-algebra structure, which is again free and finite over $R$). The assertion is the equality in $R$
--   $$\mathrm{N}_{(A \times B)/R}(x) \;=\; \mathrm{N}_{A/R}(x_1)\cdot \mathrm{N}_{B/R}(x_2),$$
--   where $\mathrm{N}_{\bullet/R}$ denotes Mathlib's algebra norm `Algebra.norm R`, i.e. the determinant of the $R$-linear endomorphism given by left multiplication by the element. Note that $A$ and $B$ are not assumed commutative; the norm is taken in the sense of the determinant of left multiplication throughout, and the hypotheses of freeness and finiteness over $R$ are what make these determinants meaningful.
--
--   This is the standard multiplicativity of the algebra norm along a direct product decomposition, in the form $\mathrm{N}(x_1,x_2)=\mathrm{N}(x_1)\mathrm{N}(x_2)$. It serves to split norm computations over a product of algebras one factor at a time, for instance across a Chinese-remainder decomposition of a finite quotient, and is used in the norm-value formula for places on curves and in a lemma comparing the norm on an algebra with the norms on two generating subalgebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_norm_prod.lean

import Mathlib.RingTheory.Norm.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.norm_prod {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B] [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B] (x : A × B) : Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by sorry
