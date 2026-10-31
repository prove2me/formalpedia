-- Prove2me | Theorems.Thm_FBMSP_corollary2_moment_bound
-- name    : FBMSP.corollary2_moment_bound
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T11:48:14.088856+00:00
-- url     : https://prove2.me/theorems/ebbcb369-37c9-46ca-8fdf-512a772f8837
-- title:
--   Corollary 2 — Moment bound
-- statement:
--   Assume nonnegative integrable predictions with finite second moment, independent integrable mean-zero error, and nonnegative realized valuations almost surely. If prediction variance is $\sigma^2$ and $\sigma\ge0$, then for every $k\ge1$,
--   $$R_\infty-R_k\le2\sqrt{\frac{2\sigma(\mathbb E[M]+\sigma)}{k}}.$$
--
--   **Author-confirmed correction.** The factor two was confirmed on October 30, 2026. This result uses the same nonnegative realized-valuation setting as corrected Theorem 3. Minimizing the proof's expression $2j\sigma/k+(\mathbb E[M]+\sigma)/j$ yields this constant. The formal proof remains open and must handle conditional truncation, boundary atoms, and the zero-variance case.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Corollary 2, p.23; proof p.46 (ec12). Factor two confirmed by the author on October 30, 2026; the nonnegative realized-valuation condition is inherited from corrected Theorem 3.

import Definitions.Def_FBMSP_Model
open MeasureTheory

namespace FBMSP

theorem corollary2_moment_bound (ν η : Measure ℝ)
    (hν : ValidPredictions ν) (hη : ValidNoise η)
    (hV : NonnegativeValuations ν η)
    (hMoment : Integrable (fun x : ℝ => x ^ 2) ν)
    (σ : ℝ) (hσ : 0 ≤ σ) (hVar : predictionVariance ν = σ ^ 2)
    (k : ℕ) (hk : 1 ≤ k) :
    segmentationLoss ν η k ≤
      2 * Real.sqrt (2 * σ * (predictionMean ν + σ) / (k : ℝ)) := by sorry

end FBMSP
