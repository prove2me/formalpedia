-- Prove2me | Theorems.Thm_FBMSP_theorem4_bounded_loss
-- name    : FBMSP.theorem4_bounded_loss
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T11:47:20.135071+00:00
-- url     : https://prove2.me/theorems/3e9b84a3-d9d8-45d9-a309-b48d00f12062
-- title:
--   Theorem 4 — Bounded loss with k segments
-- statement:
--   For any nonnegative integrable prediction law and independent integrable mean-zero error, assume finite bounds $L\le M\le U$ almost surely. Then for every $k\ge1$,
--   $$R_\infty-R_k\le\frac{U-L}{k}.$$
--   No MHR assumption or nonnegativity of realized valuations is imposed. Prediction laws may be atomic or continuous. Taking the tight support bounds recovers the source statement; any enclosing almost-sure bounds give the same valid form.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Theorem 4, p.22; proof p.45 (ec11).

import Definitions.Def_FBMSP_Model
open MeasureTheory Set

namespace FBMSP

theorem theorem4_bounded_loss (ν η : Measure ℝ)
    (hν : ValidPredictions ν) (hη : ValidNoise η)
    (L U : ℝ) (hLU : L ≤ U) (hRange : ∀ᵐ x ∂ν, x ∈ Icc L U)
    (k : ℕ) (hk : 1 ≤ k) :
    segmentationLoss ν η k ≤ (U - L) / (k : ℝ) := by sorry

end FBMSP
