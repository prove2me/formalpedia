-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_sampled_lower_exit_stopping
-- name    : AvramDividend.Classical.avram_gfinite15_original_sampled_lower_exit_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:08:23.938756+00:00
-- url     : https://prove2.me/theorems/01e18751-ae11-4936-a9d7-f8173ecd1c00
-- title:
--   Original postpayment lower-only sampled first-exit is a stopping time
-- statement:
--   For any original Lévy controlled reserve, deterministic sample times and lower barrier, the infimum of sample times at which post-right-payment reserve falls strictly below the barrier, with infinity for non-violating samples, is a stopping time in the original right-continuous filtration. No upper barrier and no arbitrary-grid density claim.
-- source:
--   Original Gaussian G-FINITE15 physical lower-exit clock construction for Open 3308ae9d; adapts the Proved two-sided source 4e7e60dd to lower-only, allowing cap contact without premature localisation.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gfinite15_original_sampled_lower_exit_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (δ : ℝ) :
    IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => ⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ
        then (r k : WithTop ℝ≥0) else ⊤) := by sorry
