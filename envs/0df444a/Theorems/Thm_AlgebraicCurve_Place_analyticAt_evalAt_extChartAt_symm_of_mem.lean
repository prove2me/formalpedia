-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_analyticAt_evalAt_extChartAt_symm_of_mem
-- name    : AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/d7776fc3-9bd2-5b89-9110-e0feb294c85b
-- title:
--   Regular at a place implies analytic in the chart
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{C}$-algebra structure such that `IsCurveOver ℂ F` holds: every nonzero $f \in F$ admits a divisor $D$ with $D(v) = \operatorname{ord}_v(f)$ at every place $v$ and $\deg D = 0$; each residue field $\kappa(v)$ is finite-dimensional over $\mathbb{C}$; and $\Omega[F/\mathbb{C}]$ is free of rank one over $F$. Here a place is a valuation subring of $F$ containing the image of $\mathbb{C}$, distinct from $F$ itself, and a principal ideal ring; $\operatorname{ord}_v(f)$ is minus the logarithm of the associated height-one-spectrum valuation of $f$, and `Place.evalAt v f` is the image of $f$ in $\kappa(v)$ pulled back to $\mathbb{C}$ along $\mathbb{C} \to \kappa(v)$ when $f$ lies in the valuation subring of $v$, and $0$ otherwise. Assume the type of places of $F$ over $\mathbb{C}$ carries a Hausdorff topology and a charted space structure over $\mathbb{C}$ in which, for every nonzero $f$ and every place $v$, the chart read $z \mapsto \mathrm{evalAt}\,(\varphi_v^{-1}(z))\,f$, with $\varphi_v$ the extended chart at $v$ for the model $\mathbb{C}$, is meromorphic at $\varphi_v(v)$ with meromorphic order equal to $\operatorname{ord}_v(f)$ in $\mathbb{Z} \cup \{\infty\}$. Then for every place $v$ and every $f$ belonging to the valuation subring of $v$, the chart read $z \mapsto \mathrm{evalAt}\,(\varphi_v^{-1}(z))\,f$ is analytic at $\varphi_v(v)$.
--
--   This is the removable-singularity step passing from meromorphy with non-negative order to honest analyticity: a function regular at a place is holomorphic at the corresponding point of the Riemann surface of places, in the chart at that point. It underlies the later chart computations on this surface, such as the continuity of chart reads, the identification of $\operatorname{ord}_v(f - f(v))$ with the analytic order of vanishing, and the local expansions of differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_analyticAt_evalAt_extChartAt_symm_of_mem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped Manifold ContDiff

theorem AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem
    (F : Type*) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (v : Place ℂ F) {f : F} (hf : f ∈ v.toValuationSubring) :
    AnalyticAt ℂ (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
      (extChartAt 𝓘(ℂ, ℂ) v v) := by sorry
