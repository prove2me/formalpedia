-- Prove2me | Theorems.Thm_ConvexOptAlg_CenterGravity_thm_2_1_vol_scaled_copy
-- name    : ConvexOptAlg.CenterGravity.thm_2_1_vol_scaled_copy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:23:53.792828+00:00
-- url     : https://prove2.me/theorems/6ead646e-0645-434f-bafc-6d036475907a
-- title:
--   Proof of Theorem 2.1, p. 246 — the shrunk copy X_ε = {(1 − ε)x* + εx : x ∈ X} has vol(X_ε) = εⁿ vol(X)
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be a convex body, $x^*\in\mathcal X$ and $\varepsilon\in[0,1]$. Set
--   $$\mathcal X_\varepsilon=\{(1-\varepsilon)x^*+\varepsilon x,\ x\in\mathcal X\}.$$
--   Then
--   $$\mathrm{vol}(\mathcal X_\varepsilon)=\varepsilon^n\,\mathrm{vol}(\mathcal X).$$
--
--   $\mathcal X_\varepsilon$ is the image of $\mathcal X$ under the homothety of centre $x^*$ and ratio $\varepsilon$. Comparing its volume with that of the localizer sets is how the proof of Theorem 2.1 finds a point of $\mathcal X_\varepsilon$ that has been cut away.
--
--   **Formalization Note** $\mathcal X_\varepsilon$ is written as the image of $\mathcal X$ under $x\mapsto(1-\varepsilon)x^*+\varepsilon x$. Volumes are extended non-negative reals, so $\varepsilon^n$ appears as the extended real $\varepsilon$ raised to the $n$-th power.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 2.1, p. 246

import Mathlib
import Definitions.Def_ConvexOptAlg_CenterGravity_Defs

open MeasureTheory
open scoped InnerProductSpace

namespace ConvexOptAlg.CenterGravity

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 2.1, p. 246: for `ε ∈ [0, 1]` and
`X_ε = {(1 - ε)x* + εx, x ∈ X}` one has `vol(X_ε) = εⁿ vol(X)`. Here `X` is the chapter's convex body and
`x* ∈ X`. -/
theorem thm_2_1_vol_scaled_copy {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (hX : IsConvexBody X)
    {xstar : EuclideanSpace ℝ (Fin n)} (hxstar : xstar ∈ X) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    volume ((fun x => (1 - ε) • xstar + ε • x) '' X) = ENNReal.ofReal ε ^ n * volume X := by sorry

end ConvexOptAlg.CenterGravity
