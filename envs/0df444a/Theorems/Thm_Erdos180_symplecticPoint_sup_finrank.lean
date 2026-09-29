-- Prove2me | Theorems.Thm_Erdos180_symplecticPoint_sup_finrank
-- name    : Erdos180.symplecticPoint_sup_finrank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:02:10.644281+00:00
-- url     : https://prove2.me/theorems/a5540953-532c-4e39-af4d-5966f3b4bccc
-- title:
--   Two distinct points span a plane
-- statement:
--   For distinct projective points $p \ne q$ of $\mathbb{F}_q^4$,
--
--   $$\dim_K (p + q) \;=\; 2.$$
--
--   $W(q)$ denotes the symplectic generalized quadrangle over $\mathbb{F}_q$, whose points are the $1$-dimensional and whose lines are the totally isotropic $2$-dimensional subspaces of $\mathbb{F}_q^4$, and $I_q$ its bipartite point-line incidence graph. $I_q$ has girth eight, $n_q = 2(q+1)(q^2+1)$ vertices and $e_q = (q+1)^2(q^2+1) \ge 2^{-4/3} n_q^{4/3}$ edges (§4 of the source). This is the basic linear-algebra fact underlying the identification, in
--   Proposition 4.2, of the common centres of two non-collinear points $y, z$ with the projective
--   points of $U^{\perp}$, where $U = y + z$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L1094-L1104

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.symplecticPoint_sup_finrank
    {p q : SymplecticPoint K} (hpq : p ≠ q) :
    Module.finrank K
      (p.1 ⊔ q.1 : Submodule K (SymplecticVector K)) = 2 := by sorry
