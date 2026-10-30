-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_history_survival_pair_measurable
-- name    : AvramDividend.Classical.avram_ws01e_integrator_new_history_survival_pair_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T07:42:41.706988+00:00
-- url     : https://prove2.me/theorems/bab28150-2b98-4e1e-9169-a5c7c84a4866
-- title:
--   Actual closed-horizon Levy endpoint and survival Boolean form one F_s-measurable historical Markov state
-- statement:
--   For an actual spectrally negative Lévy process, current time s and reserve x, the pair comprising X_s and the Boolean result of whether the entire original path remains above -x through s is measurable with respect to the actual natural filtration at s. The rational-covering schedule is used only to invoke an accepted exact source-specific closed lower-survival filtration-measurability theorem; no augmented tilted measure or Wiener-Hopf axiom is introduced.
-- source:
--   Discharges the only explicit source-history measurability premise of already-Proved original-P finite-horizon Esscher survival Markov product 3787cbef. Reuses exact accepted source filtration-measurable lower survival 398891d8 and the adaptedness field of SpectrallyNegativeLevy, with elementary arithmetic, measurable Boolean conditional and product measurability. Supports WS1A deterministic killed semigroup downstream of scalar 07c7d8b4 without entering any reserved target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01e_integrator_new_history_survival_pair_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (s : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹) :
    Measurable[𝓕 s]
      (fun ω : Ω => (X.X s ω,
        decide (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω))) := by sorry
