-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_postpayment_reserve_grid_telescope
-- name    : AvramDividend.Classical.avram_p4_f3_original_postpayment_reserve_grid_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:51:38.433864+00:00
-- url     : https://prove2.me/theorems/ecb8407a-e80b-436f-a9bd-8af8792e1de7
-- title:
--   Original finite-grid post-rightpayment reserve telescoping source identity
-- statement:
--   For any original spectrally negative Lévy X, dividend path D, and sample, the sum of finite-grid X increments less rightLimit dividend increments equals the corrected post-rightpayment reserve difference between endpoints.
-- source:
--   Formal finite-grid source reduction from the public two-clock source theorem ced98f02. Corrects binding precedence in v1 declaration, which failed publication because the second summand escaped the index binder. This supports the original fdb9a6a3 stopped Itô source-cell ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_prepost_reserve_two_clock_increment
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f3_original_postpayment_reserve_grid_telescope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range n,
      ((X.X (u (i + 1)) ω - X.X (u i) ω) -
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω))) =
    (riskProcess X x D (u n) ω -
      (rightLimit D (u n) ω - D (u n) ω)) -
    (riskProcess X x D (u 0) ω -
      (rightLimit D (u 0) ω - D (u 0) ω)) := by sorry
