-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_controlled_cap_contact_immediate_downward_at_stopping
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_controlled_cap_contact_immediate_downward_at_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:04:24.777652+00:00
-- url     : https://prove2.me/theorems/72dba662-c0cf-4ff4-8452-0ac022146c94
-- title:
--   Same-original-source controlled UBV reserve moves immediately strictly below cap after arbitrary finite stopping-time contact, including time zero
-- statement:
--   For the original unbounded-variation spectrally negative Levy process on its given filtration and the actual same-filtration nondecreasing adapted dividend strategy, every finite stopping time τ has arbitrarily short strictly positive times at which the controlled reserve U strictly decreases from U_τ. In particular, if the original reserve is at or below any real cap c at τ, it enters strictly below c arbitrarily soon after τ, even τ=0 and initial x=c. This is an almost-sure pathwise stochastic boundary property, not an occupation-time zero result, Ito-Meyer formula, or assertion that every dividend jump occurs at an interior reserve.
-- source:
--   Original Proved same-source finite-stopping downward regularity 66982d13-ea38-4a01-9f6c-49753efab1c0 and monotonicity in IsDividendStrategy; independent cap-contact helper for corrected canonical UBV core 429e17ca-5528-40b5-b593-7c03973d0706 of mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. No parent edge or milestone change.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_levy_finite_stopping_downward_regular_no_grid

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_05_ubv_controlled_cap_contact_immediate_downward_at_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, 0 < s ∧ s < ε ∧
        riskProcess X x D (τ ω + s) ω < riskProcess X x D (τ ω) ω ∧
        (riskProcess X x D (τ ω) ω ≤ c →
          riskProcess X x D (τ ω + s) ω < c) := by sorry
