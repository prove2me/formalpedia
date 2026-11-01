-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_large_right_payment_jumps_finite
-- name    : AvramDividend.Classical.avram_wave4_04b_finite_horizon_large_right_payment_jumps_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:30:39.375019+00:00
-- url     : https://prove2.me/theorems/ffbc706e-6c93-41f3-b8f7-8f89abfea031
-- title:
--   Every positive dividend-jump magnitude threshold leaves only finitely many chronological payment atoms on a finite horizon
-- statement:
--   For the genuine complete positive right-payment atom support of any adapted dividend strategy on [0,T], including time zero, the subset with jump size at least any fixed ε>0 is finite. The proof uses actual summability of all right-payment sizes, hence convergence to zero along the cofinite filter. Singular-continuous and absolutely continuous dividends remain permitted.
-- source:
--   04-B source finite-variation large-payment truncation, consequence of actual full right-support summability

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_full_right_payment_jump_support_summable
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_finite_horizon_large_right_payment_jumps_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let A : Set ℝ :=
      {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧
        0 < rightLimit D s.toNNReal ω - D s.toNNReal ω}
    ∀ ε : ℝ, 0 < ε →
      {s : A | ε ≤ rightLimit D ((s : ℝ).toNNReal) ω -
        D ((s : ℝ).toNNReal) ω}.Finite := by
  sorry
