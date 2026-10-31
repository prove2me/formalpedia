-- Prove2me | Theorems.Thm_FBMSP_corollary2_superseded_copy
-- name    : FBMSP.corollary2_superseded_copy
-- status  : Open
-- author  : @mikeh
-- created : 2026-10-30T11:49:08.309079+00:00
-- url     : https://prove2.me/theorems/67adb57b-732b-4794-9f7b-1f9b45ffd071
-- title:
--   Superseded draft copy — corrected Corollary 2
-- statement:
--   This earlier draft record is retained as a superseded copy. Its mathematical statement has also been corrected to require nonnegative realized valuations and to include the factor two:
--   $$R_\infty-R_k\le2\sqrt{\frac{2\sigma(\mathbb E[M]+\sigma)}{k}}.$$
--
--   Use **Corollary 2 — Moment bound** (FBMSP.corollary2_moment_bound) as the definitive milestone. This duplicate is not a milestone.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Retained earlier draft record of Corollary 2, p.23; updated with the author-confirmed factor two on October 30, 2026 and the nonnegative realized-valuation setting of corrected Theorem 3.

import Definitions.Def_FBMSP_Model
open MeasureTheory

namespace FBMSP

theorem corollary2_superseded_copy (ν η : Measure ℝ)
    (hν : ValidPredictions ν) (hη : ValidNoise η)
    (hV : NonnegativeValuations ν η)
    (hMoment : Integrable (fun x : ℝ => x ^ 2) ν)
    (σ : ℝ) (hσ : 0 ≤ σ) (hVar : predictionVariance ν = σ ^ 2)
    (k : ℕ) (hk : 1 ≤ k) :
    segmentationLoss ν η k ≤
      2 * Real.sqrt (2 * σ * (predictionMean ν + σ) / (k : ℝ)) := by sorry

end FBMSP
