-- Prove2me | Theorems.Thm_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card
-- name    : AlgebraicCurve.RROpens.exists_injective_ell_sub_sum_single_eq_one_of_le_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/fe67effa-5eaf-5e0f-ac25-eaa53f8a93bd
-- title:
--   General position of r-g degree-one places from a finite pool
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra satisfying `IsCurveOver K F`, i.e. every nonzero $f \in F$ has a divisor of degree $0$ recording its orders at all places, each place has residue field finite over $K$, and the module of Kähler differentials $\Omega[F/K]$ is free of rank $1$ over $F$. Here a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring; a divisor is a finitely supported $\mathbb{Z}$-valued function on places, its degree being the sum of its coefficients weighted by $\deg v = \operatorname{finrank}_K$ of the residue field of $v$, and $\ell(D)$ denotes $\operatorname{finrank}_K$ of the Riemann–Roch space of $D$. Assume given a divisor $K_c$ and a natural number $g$ for which the Riemann–Roch identity $\ell(D) - \ell(K_c - D) = \deg D + 1 - g$ holds for every divisor $D$. Let $r$ be a natural number with $2g \le r + 1$, let $S$ be a finite set of places each of degree $1$ with $r + 1 \le |S|$, and let $D$ be a divisor of degree $r$. Then there is an injective map $f \colon \mathrm{Fin}(r - g) \to$ places (truncated subtraction) with all $f(j) \in S$ and $\ell\bigl(D - \sum_j f(j)\bigr) = 1$, where each $f(j)$ is taken with coefficient $1$.
--
--   This is the general-position step underlying the description of $\mathrm{Pic}^r$ by charts indexed by $(r-g)$-tuples of degree-one places: as soon as $r+1$ such places are available, a suitable $(r-g)$-tuple can be chosen from among them, with no genericity hypothesis on the pool and no effectivity hypothesis on $D$. It is used in the constructions of sections of relative Picard schemes, via [`AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_field`](thm.html#AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_field), [`AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_finiteMapData`](thm.html#AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_finiteMapData) and [`AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_isAlgClosed`](thm.html#AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card.lean

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

theorem AlgebraicCurve.RROpens.exists_injective_ell_sub_sum_single_eq_one_of_le_card
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    {r : ℕ} (hgr : 2 * g ≤ r + 1)
    (S : Finset (Place K F)) (hS : ∀ v ∈ S, v.deg = 1) (hcard : r + 1 ≤ S.card)
    (D : Divisor K F) (hdeg : Divisor.degree D = r) :
    ∃ f : Fin (r - g) → Place K F, Function.Injective f ∧ (∀ j, f j ∈ S) ∧
      ell (D - ∑ j : Fin (r - g), Finsupp.single (f j) 1) = 1 := by sorry
