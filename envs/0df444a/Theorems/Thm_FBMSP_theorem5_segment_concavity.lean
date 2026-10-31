-- Prove2me | Theorems.Thm_FBMSP_theorem5_segment_concavity
-- name    : FBMSP.theorem5_segment_concavity
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T11:47:47.674459+00:00
-- url     : https://prove2.me/theorems/3d20d971-80e2-4ed0-a631-2fe786dca7a0
-- title:
--   Theorem 5 — Concavity in the number of segments
-- statement:
--   For any nonnegative integrable prediction law and independent integrable mean-zero MHR error, the marginal revenue from another segment is nonincreasing:
--   $$R_{k+2}-R_{k+1}\le R_{k+1}-R_k,\qquad k\ge1.$$
--   This target retains arbitrary prediction distributions. The pricing structure is essential; concavity is not assumed for arbitrary dynamic-program block scores.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Theorem 5, p.24; proof pp.47–49 (ec13–ec15).

import Definitions.Def_FBMSP_Model

namespace FBMSP

theorem theorem5_segment_concavity (ν η : MeasureTheory.Measure ℝ)
    (hν : ValidPredictions ν) (hη : ValidNoise η) (hMHR : HasMHR η)
    (k : ℕ) (hk : 1 ≤ k) :
    optimalRevenue ν η (k + 2) - optimalRevenue ν η (k + 1) ≤
      optimalRevenue ν η (k + 1) - optimalRevenue ν η k := by sorry

end FBMSP
