-- Prove2me | Theorems.Thm_DimCallCenters_QualityDriven_lemma_B_1
-- name    : DimCallCenters.QualityDriven.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:56:27.673986+00:00
-- url     : https://prove2.me/theorems/e53d491e-91cc-4847-9ec4-02322e498c2f
-- title:
--   Lemma B.1 — $P$ is strictly convex and decreasing
-- statement:
--   Let $P(x) = 1/(1 + x/h(-x))$ be the Halfin–Whitt delay function of display (11), with $h$ the hazard rate of the standard normal distribution. Then
--
--   $$
--   P \ \text{is strictly convex and strictly decreasing on } (0,\infty).
--   $$
--
--   The monotonicity is what turns a staffing level that stays below a fixed level into a delay probability that stays above the corresponding value, display (15).
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 39, Lemma B.1

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_delayFn

open Filter Topology

namespace DimCallCenters.QualityDriven

/-- Lemma B.1 (p. 39): the Halfin–Whitt delay function `P(x) = 1 / (1 + x / h(-x))` of (11) is
strictly convex and strictly decreasing on `x ∈ (0, ∞)`. -/
theorem lemma_B_1 :
    StrictConvexOn ℝ (Set.Ioi 0) DimCallCenters.Rationalized.delayFn ∧ StrictAntiOn DimCallCenters.Rationalized.delayFn (Set.Ioi 0) := by sorry

end DimCallCenters.QualityDriven
