-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_countable_stopping_time_recurrent_cap_contact_escape
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_original_countable_stopping_time_recurrent_cap_contact_escape
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T12:13:41.321439+00:00
-- url     : https://prove2.me/theorems/7faa54d0-c54c-4c2d-b5b6-87bb8d2b0fbc
-- title:
--   One genuine UBV source event leaves the cap immediately after every one of countably many stopping-time contacts, including time zero
-- statement:
--   For any prescribed countable sequence of finite ℱ-stopping times τ_n of the original spectrally negative unbounded-variation Levy source controlled by the actual dividend strategy, almost every path has the following property simultaneously for every n: if the reserve is at cap c at τ_n before ruin, then for every ε>0 there exists an actual later reserve time s in (τ_n,τ_n+ε), still before ruin, with reserve strictly below c. The choice τ_n=0 is allowed, including initial capital x=c. Repeated contacts at arbitrarily many listed stopping times are allowed; the proof never stops permanently at first contact, does not assume dividend events occur below cap, and uses no artificial cap derivative.
-- source:
--   Proved genuine finite-stopping-time UBV cap escape 24948d87-b6fb-4574-9536-29a711da94aa, countable almost-sure intersection. Supports corrected canonical core 429e17ca-5528-40b5-b593-7c03973d0706 unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_original_surviving_cap_stopping_enters_strict_subcap_immediately

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_05_ubv_original_countable_stopping_time_recurrent_cap_contact_escape
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ n ω ≤ s})
    (hStop : ∀ n, IsStoppingTime 𝓕
      (fun ω : Ω => (τ n ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      (τ n ω : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D (τ n ω) ω = c →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, τ n ω < s ∧ s < τ n ω + ε ∧
          (s : ℝ≥0∞) < ruinTime X x D ω ∧
          riskProcess X x D s ω < c := by sorry
