-- Prove2me | Theorems.Thm_DimCallCenters_EfficiencyDriven_lemma_C_1
-- name    : DimCallCenters.EfficiencyDriven.lemma_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:41:51.569376+00:00
-- url     : https://prove2.me/theorems/1283ed1c-c8c6-48f5-b2e1-1f639a1b4a9b
-- title:
--   Lemma C.1 — convexity and decrease of waiting cost
-- statement:
--   For every positive arrival rate $\lambda$ and waiting-cost model satisfying Section 2, the scaled conditional waiting cost $G_\lambda$ is strictly convex and strictly decreasing on positive real staffing offsets:
--
--   $$
--   G_\lambda\text{ is strictly convex and strictly decreasing on }(0,\infty).
--   $$
--
--   This supplies the shape of the continuous cost used in the staffing optimization framework.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 40, Lemma C.1

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Glam

namespace DimCallCenters.EfficiencyDriven

/-- Lemma C.1, p. 40. -/
theorem lemma_C_1 (M : DimCallCenters.Rationalized.WaitModel) (lam : ℝ) (hlam : 0 < lam) :
    StrictConvexOn ℝ (Set.Ioi 0) (DimCallCenters.Rationalized.Glam M lam) ∧
      StrictAntiOn (DimCallCenters.Rationalized.Glam M lam) (Set.Ioi 0) := by sorry

end DimCallCenters.EfficiencyDriven
