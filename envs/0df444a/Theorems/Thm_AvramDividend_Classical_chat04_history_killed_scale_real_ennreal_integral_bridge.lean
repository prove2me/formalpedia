-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_history_killed_scale_real_ennreal_integral_bridge
-- name    : AvramDividend.Classical.chat04_history_killed_scale_real_ennreal_integral_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:18:15.421714+00:00
-- url     : https://prove2.me/theorems/af571454-2769-4d9d-ab63-6dd178ecee50
-- title:
--   Convert the exact history-killed scale payoff between real and ENNReal expectations
-- statement:
--   For a spectrally negative Lévy process, a measurable closed-horizon nonruin event and a q-scale function with an exponential Laplace gap, the extended-nonnegative integral of the history-killed discounted scale payoff equals ENNReal.ofReal of its real integral. The previously Proved killed L² estimate establishes integrability, while scale positivity and survival measurability establish nonnegativity and strong measurability. No observation schedule is required. This converts the real killed semigroup continuity lemmas into the ENNReal language of the remaining renewal and stopped-scale identities.
-- source:
--   Proved history-killed L² bound 294fb6fa; Proved schedule-free survival measurability 55082175; Proved scale measurability; pinned Mathlib MeasureTheory.ofReal_integral_eq_lintegral_ofReal; downstream a885f0b3 and 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat04_killed_deterministic_horizon_scale_l2_bound
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_history_killed_scale_real_ennreal_integral_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) =
    ENNReal.ofReal (∫ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω ∂P) := by sorry
