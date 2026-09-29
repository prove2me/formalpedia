-- Prove2me | Theorems.Thm_AlgebraicCurve_pathIntegral_finset_sum_smul
-- name    : AlgebraicCurve.pathIntegral_finset_sum_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/8619e5ab-03ba-5acc-bb37-2aafcbe52a97
-- title:
--   Linearity of the path integral in the differential
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure making it a curve over $\mathbb{C}$ in the project's sense (principal divisors of degree zero exist for every nonzero $f$, every place has residue field finite over $\mathbb{C}$, and $\Omega[F\!\restriction\!\mathbb{C}]$ is free of rank one over $F$) and essentially of finite type over $\mathbb{C}$, and suppose the space $\mathrm{Place}\,\mathbb{C}\,F$ of places carries a Hausdorff topology with $\mathbb{C}$-charts making it an analytic manifold. Assume $hF$: for every $f \neq 0$ and every place $v$, the function $z \mapsto \mathrm{evalAt}$ of $f$ at the place $(\mathrm{extChartAt}\ v)^{-1}(z)$ is meromorphic at the chart image of $v$ with meromorphic order equal to $v.\mathrm{ord}(f) = -\log$ of the adic valuation of $f$. Let $\iota$ be a type, $s$ a finite subset of $\iota$, $c : \iota \to \mathbb{C}$, $\theta : \iota \to \Omega[F\!\restriction\!\mathbb{C}]$, and $\gamma$ a path from a place $P$ to a place $P'$. Assume that for each $i \in s$ and each $t$ the order $\mathrm{ordDifferential}$ of $\theta\,i$ at $\gamma\,t$ (the valuation at $\gamma\,t$ of the coefficient of $\theta\,i$ against $\gamma\,t$'s chosen generator $\mathrm{dCoord}$) is nonnegative, and that each $\theta\,i$, $i \in s$, admits a primitive along $\gamma$, i.e. a $g : [0,1] \to \mathbb{C}$ such that near every $t_0$ there is $\Phi$ with $\Phi' = \mathrm{readDifferential}$ of $\theta\,i$ at $\gamma\,t_0$ near the chart image of $\gamma\,t_0$ and $g\,t = \Phi(\mathrm{extChartAt}(\gamma\,t_0)(\gamma\,t))$ near $t_0$. Then $\sum_{i \in s} c\,i \cdot \theta\,i$ also admits a primitive along $\gamma$, and its path integral along $\gamma$ — the increment $g(1) - g(0)$ of a chosen primitive — equals $\sum_{i \in s} c\,i \cdot \mathrm{pathIntegral}(\theta\,i)(\gamma)$.
--
--   This is linearity of the line integral of a differential along a path, in the chart-by-chart formulation by local primitives used throughout the analytic theory of the curve $\mathrm{Place}\,\mathbb{C}\,F$; the nonnegativity hypothesis restricts to differentials regular along $\gamma$. It is used in the reciprocity statement for path integrals over loops and in the cell-dissection identity expressing a path integral as a combination of periods and residues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_pathIntegral_finset_sum_smul.lean

import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology Real
open AlgebraicCurve Complex Set

universe u

theorem AlgebraicCurve.pathIntegral_finset_sum_smul
    (F : Type u) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (ι : Type) (s : Finset ι) (c : ι → ℂ) (θ : ι → Ω[F⁄ℂ])
    {P P' : Place ℂ F} (γ : Path P P')
    (hreg : ∀ i ∈ s, ∀ t, 0 ≤ (γ t).ordDifferential (θ i))
    (hprim : ∀ i ∈ s, ∃ g, IsPrimitiveAlong (θ i) γ g) :
    (∃ g, IsPrimitiveAlong (∑ i ∈ s, c i • θ i) γ g) ∧
      pathIntegral (∑ i ∈ s, c i • θ i) γ = ∑ i ∈ s, c i * pathIntegral (θ i) γ := by sorry
