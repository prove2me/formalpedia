-- Prove2me | Theorems.Thm_FBMSP_corollary1_segment_price_bounds
-- name    : FBMSP.corollary1_segment_price_bounds
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T04:56:54.181434+00:00
-- url     : https://prove2.me/theorems/b842629b-ad90-4dcf-a109-996d9447b76f
-- title:
--   Corollary 1 — Bounds on an optimal segment price
-- statement:
--   Consider a nonempty finite segment with nonnegative distinct predicted values and positive weights normalized to sum to one, under integrable mean-zero MHR error. If every individual least optimal price lies between $L$ and $U$, some nonnegative price that maximizes total segment revenue also lies in $[L,U]$.
--
--   Taking the smallest and largest individual optimal prices as $L,U$ recovers the finite-support form of the source's bound. The existence formulation handles ties without claiming that every segment optimizer must lie in the interval.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Corollary 1, p.17; proof p.43 (ec9).

import Definitions.Def_FBMSP_Model

namespace FBMSP

/-- Corollary 1 for a finite segment.  Bounds enclosing all individual least
optimal prices also enclose an attaining optimal price for the segment.
Draft statement; proof remains open. -/
theorem corollary1_segment_price_bounds {n : ℕ}
    (η : MeasureTheory.Measure ℝ) (hnoise : ValidNoise η) (hmhr : HasMHR η)
    (μ w : Fin n → ℝ) (hmarket : ValidFiniteMarket μ w)
    (L U : ℝ)
    (hbounds : ∀ i, L ≤ singlePrice η (μ i) ∧ singlePrice η (μ i) ≤ U) :
    ∃ p : ℝ, 0 ≤ p ∧ L ≤ p ∧ p ≤ U ∧
      ∀ q : ℝ, 0 ≤ q →
        blockRevenue η μ w 0 n q ≤ blockRevenue η μ w 0 n p := by sorry

end FBMSP
