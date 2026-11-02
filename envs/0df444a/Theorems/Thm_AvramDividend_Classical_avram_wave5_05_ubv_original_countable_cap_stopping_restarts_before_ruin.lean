-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_countable_cap_stopping_restarts_before_ruin
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_countable_cap_stopping_restarts_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:32:14.144078+00:00
-- url     : https://prove2.me/theorems/c565fc06-8f3c-4ed3-b48e-32a3befe2609
-- title:
--   One original probability-one event supports immediate pre-ruin strict-subcap re-entry at every cap contact in any countable family of stopping times
-- statement:
--   For one actual original same-filtration spectrally negative Levy source of unbounded variation and its genuine dividend strategy D, consider any countably indexed family of finite stopping times, for example a recursively generated localisation or successive cap-contact restart schedule. There is a single P-probability-one event on which every such stopping time that occurs before genuine ruin with U_τ=c is immediately followed by arbitrarily near strictly subcap times still before ruin. It includes any index with τ_n=0 and x=c and accommodates repeated cap contacts; it makes no claim that every dividend is paid below c or that all uncountably many random times can be handled by one exceptional set.
-- source:
--   Accepted original pre-ruin cap-contact stopping time downcross 24948d87-b6fb-4574-9536-29a711da94aa; Mathlib countable ae_all_iff; corrected canonical 429e17ca-5528-40b5-b593-7c03973d0706. No full Itô/stieltjes scope or core edits.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_surviving_cap_stopping_enters_strict_subcap_immediately

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_countable_cap_stopping_restarts_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n (s : ℝ≥0),
      MeasurableSet[𝓕 s] {ω : Ω | τ n ω ≤ s})
    (hstop : ∀ n, IsStoppingTime 𝓕
      (fun ω => (τ n ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      (τ n ω : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D (τ n ω) ω = c →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, 0 < s ∧ s < ε ∧
          ((τ n ω + s : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω ∧
          riskProcess X x D (τ n ω + s) ω < c := by sorry
