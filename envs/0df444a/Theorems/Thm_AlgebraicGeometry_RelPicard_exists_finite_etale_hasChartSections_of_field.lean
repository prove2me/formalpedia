-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_etale_hasChartSections_of_field
-- name    : AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/47614f57-1602-5f0e-a6e8-cca23ffb3931
-- title:
--   Chart sections for a pointed curve over a field after a finite étale extension
-- statement:
--   Let $F$ be a field and let $c : C \to \operatorname{Spec} F$ be a proper morphism of schemes which is smooth of relative dimension $1$ and geometrically integral, equipped with a section $\varepsilon$, i.e. a morphism $\varepsilon : \operatorname{Spec} F \to C$ with $c \circ \varepsilon = \mathrm{id}$. Assume that for every $m_0 \in \mathbb{N}$ there is a `FiniteMapData` $\mathfrak{F}$ for $c$ and $\varepsilon$ — a pair of affine opens $U, V$ covering $C$ with $U$ the complement of the image of $\varepsilon$, sections $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ whose basic opens both equal $U \cap V$ and whose restrictions are mutually inverse there, with $F[T] \to \Gamma(C,U)$, $T \mapsto f$, and $F[T] \to \Gamma(C,V)$, $T \mapsto g$, finite, and with a degree $m = \mathfrak{F}.m$ such that for every local $F$-algebra $S$ and every $s \in S$ the level set $S \otimes_F \Gamma(C,U)/(1 \otimes f - s \otimes 1)$ is finite free of rank $m$ over $S$ — whose degree satisfies $m_0 \le m$ and with $m$ invertible in $F$. The conclusion asserts the existence of an $F$-algebra $R'$ that is finite, étale, faithfully flat, Noetherian and reduced, natural numbers $n, g, r$ with $2g < r$, and a family $\gamma : \mathrm{Fin}\,n \to \mathrm{Fin}(r-g) \to$ (sections of the base change $C_{R'} \to \operatorname{Spec} R'$) satisfying `HasChartSections`: for every algebraically closed field $k$ and every $k$-point $s$ of $\operatorname{Spec} R'$ there are a field extension $L/k$, a `CurveModel` $M$ over $k$ with function field $L$ and an isomorphism $e$ of $M.C$ with the fibre $C_{R'} \times_{R'} k$ compatible with the structure morphisms, such that Riemann–Roch holds on $L$ with a canonical divisor and the genus $g$, and for every effective divisor $D$ of degree $r$ on $L$ some index $i \le n$ has $\ell\bigl(D - \sum_{j} (\text{place of } \gamma_{i j} \text{ in the fibre})\bigr) = 1$.
--
--   This supplies, over a base field, the chart data used to represent the relative $\mathrm{Pic}^0$ of a pointed smooth proper curve: a finite étale cover of the base over which enough tuples of sections in general position exist, uniformly over all geometric fibres. It is the field case of the corresponding statement over a discrete valuation ring and is used in the analysis of the special fibre of the Jacobian of $X_1(p)$ over $\mathbb{Z}/p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_finite_etale_hasChartSections_of_field.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra

theorem AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_field
    (F : Type u) [Field F]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of F)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of F))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m ∧ IsUnit (𝔉.m : F)) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra F R') (_ : Module.Finite F R')
      (_ : Algebra.Etale F R') (_ : Module.FaithfullyFlat F R') (_ : IsNoetherianRing R') (_ : _root_.IsReduced R')
      (n g r : ℕ) (_ : 2 * g < r)
      (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange F c R')),
      HasChartSections (baseChange F c R') γ := by sorry
