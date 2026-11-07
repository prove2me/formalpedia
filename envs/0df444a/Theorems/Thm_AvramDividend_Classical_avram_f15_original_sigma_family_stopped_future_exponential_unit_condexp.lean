-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f15_original_sigma_family_stopped_future_exponential_unit_condexp
-- name    : AvramDividend.Classical.avram_f15_original_sigma_family_stopped_future_exponential_unit_condexp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:01:21.268766+00:00
-- url     : https://prove2.me/theorems/83a12ba4-2b14-4668-9e92-691b911cf3be
-- title:
--   Original finite-horizon dividend stop family inherits exact compensated Lévy exponential conditional mean
-- statement:
--   For every original right-continuous dividend localiser σ_k below ruinTime ∧ n, the future compensated Lévy exponential over any positive or zero lag is integrable and has conditional mean one given the right-continuous stopped history. This is the exact same Ω, P, X and stopping-clock family needed to build the compensated jump martingales of original pure-jump Itô–Meyer.
-- source:
--   Source-exact instantiation of the established bounded stopped compensated exponential conditional identity 731576f3 and original sigma-family boundedness cb700d07. The stochastic information is conditional and remains on the original sample space.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f14_original_sigma_family_bounded_and_preruin
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_compensated_exponential_unit_condExp

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_f15_original_sigma_family_stopped_future_exponential_unit_condexp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ k,
      Integrable (fun ω => Real.exp
        (θ * (X.X (σ k ω + h) ω - X.X (σ k ω) ω) -
          (h : ℝ) * X.ψ θ)) P ∧
      (P[(fun ω => Real.exp
        (θ * (X.X (σ k ω + h) ω - X.X (σ k ω) ω) -
          (h : ℝ) * X.ψ θ)) |
          (hσstop k).measurableSpace] =ᵐ[P] (fun _ => (1 : ℝ))) := by sorry
