-- Prove2me | Theorems.Thm_AlgebraicCurve_RROpens_exists_finset_subset_ell_sub_sum_single_eq_zero
-- name    : AlgebraicCurve.RROpens.exists_finset_subset_ell_sub_sum_single_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/19e2d05d-1ebb-5e21-847d-ee4485882fdd
-- title:
--   Riemann–Roch descent: ℓ(G-T)=0 for ℓ(G) places in a prescribed infinite set
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field extension of $K$ which is a curve over $K$ in the sense of the class `IsCurveOver`: every nonzero $f \in F$ has a divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ at every place and $\deg D = 0$, every place $v$ has residue field finite over $K$, and the module of Kähler differentials $\Omega[F/K]$ is free of rank one over $F$. Here a place is a valuation subring of $F$ containing the image of $K$, different from $F$ itself, and a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$, with degree the sum of its values weighted by the residue degrees, and $\ell(D)$ denotes the $K$-dimension of the Riemann–Roch space of $D$. Fix a divisor $K_C$ and a natural number $g$ such that the Riemann–Roch identity $\ell(D) - \ell(K_C - D) = \deg D + 1 - g$ holds for every divisor $D$. Then for every divisor $G$ and every infinite set $S$ of places there exists a finite set $T$ of places, contained in $S$, with exactly $\ell(G)$ elements, such that $\ell\bigl(G - \sum_{v \in T} v\bigr) = 0$, the subtracted divisor being the effective divisor taking value $1$ at each element of $T$.
--
--   This is the standard general-position statement obtained by subtracting points one at a time from a divisor until its Riemann–Roch space is reduced to zero, with the points constrained to lie in a prescribed infinite set of places. It is used in the curve-theoretic input to the construction of non-special divisors, notably by [`AlgebraicCurve.RROpens.exists_degree_eq_sub_one_and_ell_eq_zero`](thm.html#AlgebraicCurve.RROpens.exists_degree_eq_sub_one_and_ell_eq_zero), and in the choices of places in general position made in the study of specialisations on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RROpens_exists_finset_subset_ell_sub_sum_single_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.exists_finset_subset_ell_sub_sum_single_eq_zero
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (G : Divisor K F) (S : Set (Place K F)) (hS : S.Infinite) :
    ∃ T : Finset (Place K F), (↑T : Set (Place K F)) ⊆ S ∧ T.card = ell G ∧
      ell (G - ∑ v ∈ T, Finsupp.single v 1) = 0 := by sorry
