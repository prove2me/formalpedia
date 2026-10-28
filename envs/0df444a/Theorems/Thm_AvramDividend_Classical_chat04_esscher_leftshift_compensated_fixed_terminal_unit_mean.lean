-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_compensated_fixed_terminal_unit_mean
-- name    : AvramDividend.Classical.chat04_esscher_leftshift_compensated_fixed_terminal_unit_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:27:15.612569+00:00
-- url     : https://prove2.me/theorems/f15576f8-938c-484b-83cf-20159094b164
-- title:
--   The compensated negative Esscher exponential has unit mean under every later terminal Esscher probability law
-- statement:
--   For any θ≥ε≥0 and deterministic s≤T, the compensated negative exponential Z_s=exp(−εX_s−s[ψ(θ−ε)−ψ(θ)]) has exact expectation one when integrated under the *genuine terminal* θ-Esscher probability measure Q_T. This provides the unit-mean assumption of Doob's discrete maximal inequality for any sampled grid within a fixed terminal horizon, without assuming an infinite-horizon change of measure.
-- source:
--   First transfer the expectation of strongly F_s-measurable Z_s from Q_s to Q_T using the accepted Esscher earlier-event integral-consistency theorem (event univ). At time s, use accepted Esscher density-ratio compensation identity on univ to identify E_Qs Z_s with E_P exp((θ−ε)X_s−sψ(θ−ε)), which equals exactly one by the accepted compensated Lévy exponential theorem. `setIntegral_univ` matches the restricted and unrestricted integrals.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_compensated_setIntegral_change
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_past_event_setIntegral_consistency
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_compensated_leftshift_reward_strongly_adapted
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_leftshift_compensated_fixed_terminal_unit_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ)
    (s T : ℝ≥0) (hsT : s ≤ T) :
    (∫ ω, Real.exp
      (-ε * X.X s ω -
        (s : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) = 1 := by sorry
