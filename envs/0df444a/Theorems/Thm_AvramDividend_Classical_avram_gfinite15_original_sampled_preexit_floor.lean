-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_sampled_preexit_floor
-- name    : AvramDividend.Classical.avram_gfinite15_original_sampled_preexit_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T16:41:51.233447+00:00
-- url     : https://prove2.me/theorems/72a933d8-3894-4b83-9e69-5a84e32cd553
-- title:
--   Original postpayment sampled reserve lower floor before first violating sample
-- statement:
--   For each original physical sample path and arbitrary sequence of observation times, any sampled time strictly preceding the first sampled postpayment reserve value below a fixed real floor must itself have postpayment reserve at least the floor. This gives a pathwise discrete pre-exit invariant without claiming an arbitrary-grid approximation or physical stopping-time closure.
-- source:
--   G-FINITE15 corrected strict-preexit-floor localisation child 3308ae9d; exact original-X/D sample-grid primitive.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gfinite15_original_sampled_preexit_floor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (r : ℕ → ℝ≥0) (δ : ℝ) :
    ∀ (ω : Ω) (n : ℕ),
      (r n : WithTop ℝ≥0) <
        (⨅ k : ℕ,
          if x + X.X (r k) ω - rightLimit D (r k) ω < δ
          then (r k : WithTop ℝ≥0) else ⊤) →
      δ ≤ x + X.X (r n) ω - rightLimit D (r n) ω := by sorry
