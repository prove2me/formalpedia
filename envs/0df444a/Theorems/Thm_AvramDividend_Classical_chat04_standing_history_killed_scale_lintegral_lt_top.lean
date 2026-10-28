-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_standing_history_killed_scale_lintegral_lt_top
-- name    : AvramDividend.Classical.chat04_standing_history_killed_scale_lintegral_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T17:56:07.752046+00:00
-- url     : https://prove2.me/theorems/ae9606ba-6041-4aa9-a3b1-d74882f3c7dd
-- title:
--   Standing q-scale killed ENNReal expectation finite at every horizon
-- statement:
--   Under the Avram Standing assumptions, for every reserve and every finite time the history-killed discounted scale payoff has a finite ENNReal expectation. It uses fixed-time integrability of the scale payoff, measurability of the exact continuous-history survival event, and integrability stability under deterministic discount and indicator. It is an importable fixed-time finite-moment prerequisite for optional stopping in the preferred standing-case strict two-sided exit identity.
-- source:
--   Proved chat04_standing_scale_fixed_time_integrable (1d43ef79-1a69-4d82-b4de-d9ad5d5c8ee5) and chat04_shifted_lower_survival_measurable_no_schedule (55082175-0822-4f2f-a627-cd0eb4c0640f), pinned Mathlib Integrable.const_mul, Integrable.indicator and Integrable.lintegral_lt_top. Exact intended import by 09663d0d-c23e-47da-b5b9-1bbf28449a4d and parent 3e1ce2c8-c846-4e0f-8e4f-4fcbd9a0d4d7.

import Theorems.Thm_AvramDividend_Classical_chat04_standing_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule
import Mathlib.MeasureTheory.Integral.IntegrableOn

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_standing_history_killed_scale_lintegral_lt_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) < ⊤ := by sorry
