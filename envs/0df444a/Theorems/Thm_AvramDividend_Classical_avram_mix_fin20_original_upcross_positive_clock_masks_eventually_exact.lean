-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin20_original_upcross_positive_clock_masks_eventually_exact
-- name    : AvramDividend.Classical.avram_mix_fin20_original_upcross_positive_clock_masks_eventually_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:27:33.347528+00:00
-- url     : https://prove2.me/theorems/e248e4ad-dfd1-4418-a523-81f93a86cc2f
-- title:
--   Original mixed finite activity spatial stopping clocks eventually preserve zero-versus-positive masks
-- statement:
--   For the original spectrally negative Levy process, any bounded right-continuous stopped clock admits genuine upper-exit spatial stopped clocks at original filtration, dominated by the clock and with source X.X clipped at j+1, eventually literally equal pathwise. In particular the positive-time indicators of local clocks agree eventually, needed to pass initial events and time-zero payments by nonnegative Fatou. Derived directly from Proved b2e939f7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_any_clock_upcross_localisation
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin20_original_upcross_positive_clock_masks_eventually_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℝ≥0)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ n) :
    ∃ κ : ℕ → Ω → ℝ≥0,
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (κ k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, κ k ω ≤ ρ ω) ∧
      (∀ k ω, X.X (κ k ω) ω ≤ (k : ℝ) + 1) ∧
      (∀ ω, ∀ᶠ k : ℕ in atTop,
        κ k ω = ρ ω ∧
          (κ k ω ≠ 0 ↔ ρ ω ≠ 0)) := by sorry
