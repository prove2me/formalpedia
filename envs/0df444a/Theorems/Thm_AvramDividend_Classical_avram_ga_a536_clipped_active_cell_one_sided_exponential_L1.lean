-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a536_clipped_active_cell_one_sided_exponential_L1
-- name    : AvramDividend.Classical.avram_ga_a536_clipped_active_cell_one_sided_exponential_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:32:43.548944+00:00
-- url     : https://prove2.me/theorems/e698d792-4ff4-4429-b3f1-5a8febfd38d8
-- title:
--   Stopped active-cell value difference has integrable positive part under one-sided exponential bound
-- statement:
--   For a discounted cell with an inactive endpoint-cancellation branch or an active branch with a lower bound on the prepayment value and an exponential upper bound on the postpayment value, the positive part of the cell value difference is integrable when the exponential endpoint moment and measurability hold.
-- source:
--   Pointwise max(E*(w(Z)-w(Y)),0) ≤ K*exp(theta*Z)+B on active cells; zero on inactive; finite measure and integrable exponential moment.

import Mathlib
open MeasureTheory Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_ga_a536_clipped_active_cell_one_sided_exponential_L1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (w : ℝ → ℝ) (E Y Z : Ω → ℝ) (θ K B : ℝ)
    (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hE : ∀ᵐ ω ∂P, 0 ≤ E ω ∧ E ω ≤ 1)
    (hCell : ∀ᵐ ω ∂P, Z ω = Y ω ∨
      (-B ≤ w (Y ω) ∧ 0 < Z ω ∧
        w (Z ω) ≤ K * Real.exp (θ * Z ω)))
    (hExp : Integrable (fun ω => Real.exp (θ * Z ω)) P)
    (hMeas : AEStronglyMeasurable
      (fun ω => max (E ω * (w (Z ω) - w (Y ω))) (0 : ℝ)) P) :
    Integrable (fun ω => max (E ω * (w (Z ω) - w (Y ω))) (0 : ℝ)) P := by sorry
