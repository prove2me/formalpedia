-- Prove2me | Theorems.Thm_ConvexOptAlg_Ellipsoid_volume_scaledCopy
-- name    : ConvexOptAlg.Ellipsoid.volume_scaledCopy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:31:20.757297+00:00
-- url     : https://prove2.me/theorems/3a34afed-60fc-4c0b-b8e8-334e5db38589
-- title:
--   §2.1, proof of Theorem 2.1, p. 246 — vol(X_ε) = εⁿ vol(X) for X_ε = (1 − ε)x* + εX, ε ∈ [0, 1]
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be a convex body, let $f$ be continuous and convex on $\mathcal X$, let $x^*\in\mathcal X$ minimize $f$, and let $\varepsilon\in[0,1]$. For $\mathcal X_\varepsilon=\{(1-\varepsilon)x^*+\varepsilon x: x\in\mathcal X\}$,
--
--   $$
--   \mathrm{vol}(\mathcal X_\varepsilon)=\varepsilon^n\,\mathrm{vol}(\mathcal X).
--   $$
--
--   In the proofs of Theorems 2.1 and 2.4 this compares the volume of a shrunken copy of the constraint set, all of whose points are nearly optimal, with the volume of the current localizer.
--
--   **Formalization Note** $\mathrm{vol}$ is Lebesgue (outer) measure on `Fin n → ℝ`, with values in $[0,\infty]$. The convex-body and minimizer hypotheses come from the chapter setting and the proof of Theorem 2.1.
-- source:
--   Bubeck, arXiv:1405.4980v2, §2.1, proof of Theorem 2.1, p. 246

import Mathlib
import Definitions.Def_ConvexOptAlg_Ellipsoid_Defs

namespace ConvexOptAlg.Ellipsoid

open MeasureTheory

/-- Bubeck, arXiv:1405.4980v2, §2.1, proof of Theorem 2.1, p. 246: for a convex body `X`,
a minimizer `x∗` of `f` on `X`, and `ε ∈ [0, 1]`, the scaled copy
`X_ε = {(1 − ε)x∗ + εx : x ∈ X}` has `vol(X_ε) = εⁿ vol(X)`
(Lebesgue measure on `ℝⁿ = Fin n → ℝ`). -/
theorem volume_scaledCopy {n : ℕ} (X : Set (Fin n → ℝ)) (hX : IsConvexBody X)
    (f : (Fin n → ℝ) → ℝ) (hfcont : ContinuousOn f X) (hfconv : ConvexOn ℝ X f)
    (xstar : Fin n → ℝ) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    volume (scaledCopy X xstar ε) = ENNReal.ofReal (ε ^ n) * volume X := by sorry

end ConvexOptAlg.Ellipsoid
