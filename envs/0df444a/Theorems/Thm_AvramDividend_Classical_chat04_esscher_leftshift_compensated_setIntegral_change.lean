-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_compensated_setIntegral_change
-- name    : AvramDividend.Classical.chat04_esscher_leftshift_compensated_setIntegral_change
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:29:08.29399+00:00
-- url     : https://prove2.me/theorems/76e214d0-139a-4b4e-ac9f-16f9d764d360
-- title:
--   Exact compensation cancellation for an Esscher martingale density ratio on any event
-- statement:
--   For an arbitrary measurable event A at any deterministic time t, integration of the compensated negative exponential ratio exp(−ε X_t−t[ψ(θ−ε)−ψ(θ)]) under the genuine θ-Esscher law equals integration of the compensated (θ−ε)-Esscher exponential exp((θ−ε)X_t−tψ(θ−ε)) under the original probability law. This is a Radon–Nikodym identity on *sets*, enabling the old compensated-exponential martingale to be transferred to the compatible finite θ-Esscher laws.
-- source:
--   Use the pinned setIntegral_withDensity_eq_setIntegral_toReal_smul (which handles restricted integrals directly), strict positive finite measurable exponential density from X.adapted.measurable, and elementary real exponential algebra. The identity is valid without root, variation or Standing assumptions and makes no global tilted-law construction.

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Process.Adapted
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_leftshift_compensated_setIntegral_change
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ ε : ℝ)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω in A,
      Real.exp (-ε * X.X t ω -
        (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) =
    (∫ ω in A,
      Real.exp ((θ - ε) * X.X t ω -
        (t : ℝ) * X.ψ (θ - ε)) ∂P) := by sorry
