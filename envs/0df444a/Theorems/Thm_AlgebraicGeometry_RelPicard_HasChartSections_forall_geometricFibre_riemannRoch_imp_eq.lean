-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_HasChartSections_forall_geometricFibre_riemannRoch_imp_eq
-- name    : AlgebraicGeometry.RelPicard.HasChartSections.forall_geometricFibre_riemannRoch_imp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/2f10e771-b450-5296-aba7-5ba9ee91bb6b
-- title:
--   Chart sections pin the genus of every geometric fibre
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c \colon C \to \operatorname{Spec} R$ a morphism, let $n, g, r$ be natural numbers, and let $\gamma$ assign to each $i \in \mathrm{Fin}\,n$ and $j \in \mathrm{Fin}\,(r-g)$ a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Assume `HasChartSections c γ`: for every algebraically closed field $k$ and every $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$ there are a field $L$ with a $k$-algebra structure, a `CurveModel k L` (an integral scheme $M.C$ with a proper morphism to $\operatorname{Spec} k$ that is smooth of relative dimension $1$, a ring isomorphism of $L$ with its function field compatible with $k$, and a bijection of its closed points with the places of $L/k$ matching stalks with valuation rings, every finite set of points lying in an affine open) and an isomorphism $e \colon M.C \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ with $e$ followed by the second projection equal to the structure morphism, such that both: some divisor $K_c$ of $L/k$ satisfies $\ell(D) - \ell(K_c - D) = \deg D + 1 - g$ for all divisors $D$, and every effective divisor $D$ of degree $r$ admits an index $i$ with $\ell\big(D - \sum_j (\text{place of the fibre point of } \gamma_{ij} \text{ at } s)\big) = 1$; here divisors are finitely supported $\mathbb{Z}$-valued functions on places, $\deg$ is the weighted sum of local degrees, and $\ell(D)$ is the $k$-dimension of the Riemann–Roch space of $D$. The conclusion: for every algebraically closed field $k$, every $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$, every field $L$ with a $k$-algebra structure, every `CurveModel k L` $M$, every isomorphism $e \colon M.C \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ with $e$ followed by the second projection equal to $M$'s structure morphism, every divisor $K_c$ of $L/k$ and every natural number $g'$, if $\ell(D) - \ell(K_c - D) = \deg D + 1 - g'$ for all divisors $D$, then $g' = g$.
--
--   The statement says that the genus occurring in the chart-section hypothesis is the Riemann–Roch genus of every geometric fibre of $c$, in whatever smooth proper model and whatever function field that fibre is presented. It supplies the constant-genus input of the relative Picard chart constructions, and is cited by [`AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced`](thm.html#AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced) and [`AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced`](thm.html#AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_HasChartSections_forall_geometricFibre_riemannRoch_imp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.HasChartSections.forall_geometricFibre_riemannRoch_imp_eq
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {n g r : ℕ} {γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    (hγ : HasChartSections c γ) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g := by sorry
