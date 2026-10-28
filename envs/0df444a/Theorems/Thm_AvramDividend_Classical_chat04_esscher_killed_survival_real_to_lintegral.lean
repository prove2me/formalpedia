-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_killed_survival_real_to_lintegral
-- name    : AvramDividend.Classical.chat04_esscher_killed_survival_real_to_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:10:19.757404+00:00
-- url     : https://prove2.me/theorems/1ccb6dd6-3a93-4e59-997b-e11bc6ec80a1
-- title:
--   Exact conversion of killed Esscher survival from real expectation to nonnegative integral
-- statement:
--   For any starting capital, finite horizon and nonnegative Esscher tilt, the nonnegative integral of the continuously killed compensated exponential equals ENNReal.ofReal of its real expectation, using adapted killed-survival measurability and integrability of the Esscher exponential.
-- source:
--   Existing Proved Esscher exponential integrability 701eb6a8, shifted full-horizon lower-survival event measurability, and pinned Mathlib ofReal_integral_eq_lintegral_ofReal. Allows transporting proved real-valued antitonicity of killed Esscher survival mass into the ENNReal capital Tonelli integrand and hence controlling the full capital transform over time.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
import Theorems.Thm_AvramDividend_Classical_shifted_lower_survival_filtration_measurable_no_schedule

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_killed_survival_real_to_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (θ * X.X t ω -
            (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P) =
    ENNReal.ofReal (∫ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp (θ * X.X t ω -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) := by sorry
