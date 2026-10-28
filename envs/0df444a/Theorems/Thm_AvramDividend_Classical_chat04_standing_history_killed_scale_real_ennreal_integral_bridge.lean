-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_standing_history_killed_scale_real_ennreal_integral_bridge
-- name    : AvramDividend.Classical.chat04_standing_history_killed_scale_real_ennreal_integral_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T18:04:41.488713+00:00
-- url     : https://prove2.me/theorems/6275ef80-8f31-49ce-ae1f-8d351ec7aceb
-- title:
--   Standing killed q-scale real to ENNReal integral bridge without growth hypothesis
-- statement:
--   Standing assumptions and exact-history killing; no exponential growth witness. The history-killed discounted q-scale ENNReal expectation exactly equals ENNReal.ofReal of the corresponding real expectation. Fixed-time scale integrability and schedule-free survival measurability supply the Bochner integrability, while survival forces nonnegative reserve at the terminal horizon. This exact adapter is intended to be imported by 09663d0d-c23e-47da-b5b9-1bbf28449a4d on the active two-sided exit dependency path.
-- source:
--   Proof imports Proved chat04_standing_scale_fixed_time_integrable, Proved chat04_shifted_lower_survival_measurable_no_schedule, and pinned Mathlib ofReal_integral_eq_lintegral_ofReal. Direct downstream theorem UUID 09663d0d-c23e-47da-b5b9-1bbf28449a4d; supports killed renewal identity and ultimately 3e1ce2c8-c846-4e0f-8e4f-4fcbd9a0d4d7.

import Theorems.Thm_AvramDividend_Classical_chat04_standing_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_standing_history_killed_scale_real_ennreal_integral_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) =
    ENNReal.ofReal (∫ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω ∂P) := by sorry
