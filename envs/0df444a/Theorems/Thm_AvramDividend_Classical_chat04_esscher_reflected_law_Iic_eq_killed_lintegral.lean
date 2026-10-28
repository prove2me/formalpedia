-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_reflected_law_Iic_eq_killed_lintegral
-- name    : AvramDividend.Classical.chat04_esscher_reflected_law_Iic_eq_killed_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:41:04.005599+00:00
-- url     : https://prove2.me/theorems/7c5cad30-cdca-4d60-ac02-e210a8d61815
-- title:
--   Esscher pushforward reflected-infimum CDF equals the actual weighted killed survival integral
-- statement:
--   For each finite horizon, any Esscher parameter and initial reserve x, the pushforward of the exponential-weighted original Lévy measure by the negative running infimum assigns to (−∞,x] exactly the nonnegative original-measure integral of the terminal compensated exponential over paths staying above −x throughout the horizon. This is the true finite-horizon CDF identification, independent of a global change of measure and of the q-scale exit identity.
-- source:
--   Apply existing `levy_running_infimum_measurable`, the Proved pointwise `chat04_reflected_infimum_Iic_iff_survival`, and the Proved full-history survival measurable-set lemma. Mathlib Measure.map_apply, withDensity_apply and lintegral_indicator convert the pushforward CDF exactly into the weighted killed-survival integral. This connects to the finite-horizon Esscher probability law and Stieltjes right continuity.

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_reflected_law_Iic_eq_killed_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ x : ℝ) :
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))).map (fun ω : Ω => -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) (Iic x) =
    (∫⁻ ω, {ω : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}.indicator (fun ω : Ω => ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) ω ∂P) := by sorry
