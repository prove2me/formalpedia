-- Prove2me | Theorems.Thm_ConvexOptAlg_CenterGravity_thm_2_1_volume_decay
-- name    : ConvexOptAlg.CenterGravity.thm_2_1_volume_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T16:23:55.797441+00:00
-- url     : https://prove2.me/theorems/669431d5-59f4-4583-bc9f-1721cf457a84
-- title:
--   Proof of Theorem 2.1, p. 246 — if every w_s ≠ 0, the center of gravity method has vol(S_{t+1}) ≤ (1 − 1/e)^t vol(X)
-- statement:
--   Let $\mathcal X\subset\mathbb R^n$ be a convex body, $f:\mathcal X\to[-B,B]$ continuous and convex, and $(\mathcal S_t,c_t,w_t)_{t\ge1}$ a run of the center of gravity method on $\mathcal X$ for $f$. Let $t\ge0$ and suppose $w_s\ne0$ for every $1\le s\le t$. Then
--   $$\mathrm{vol}(\mathcal S_{t+1})\le\Big(1-\frac1e\Big)^t\,\mathrm{vol}(\mathcal X).$$
--
--   The volume of the localizer set decreases geometrically, by a factor at least $1-1/e$ per query; this is the step of the proof of Theorem 2.1 that turns Grünbaum's inequality into a convergence rate.
--
--   **Formalization Note** The hypothesis $w_s\ne0$ is the book's "without loss of generality" reduction made just before this display (a zero subgradient means $c_s$ is already optimal). Volumes are extended non-negative reals and $1/e$ is written $e^{-1}$.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 2.1, p. 246 (display following (2.2))

import Mathlib
import Definitions.Def_ConvexOptAlg_CenterGravity_Defs

open MeasureTheory
open scoped InnerProductSpace

namespace ConvexOptAlg.CenterGravity

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 2.1, p. 246: if `w_s ≠ 0` for every `s ≤ t` (the page's
"without loss of generality" reduction), then a run of the center of gravity method satisfies
`vol(S_{t+1}) ≤ (1 - 1/e)^t vol(X)`. Standing assumptions of Ch. 2: `X` a convex body, `f` continuous,
convex and `[-B, B]`-valued on `X`. -/
theorem thm_2_1_volume_decay {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (hX : IsConvexBody X)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ} (hfB : ∀ x ∈ X, |f x| ≤ B)
    (hfc : ContinuousOn f X) (hfconv : ConvexOn ℝ X f)
    {S : ℕ → Set (EuclideanSpace ℝ (Fin n))} {c w : ℕ → EuclideanSpace ℝ (Fin n)}
    (hrun : IsCenterOfGravityRun X f S c w) (t : ℕ)
    (hw : ∀ s : ℕ, 1 ≤ s → s ≤ t → w s ≠ 0) :
    volume (S (t + 1)) ≤ ENNReal.ofReal ((1 - Real.exp (-1)) ^ t) * volume X := by sorry

end ConvexOptAlg.CenterGravity
