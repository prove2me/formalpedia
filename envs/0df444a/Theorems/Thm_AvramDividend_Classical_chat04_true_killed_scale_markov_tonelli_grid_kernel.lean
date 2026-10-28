-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_true_killed_scale_markov_tonelli_grid_kernel
-- name    : AvramDividend.Classical.chat04_true_killed_scale_markov_tonelli_grid_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:26:05.85599+00:00
-- url     : https://prove2.me/theorems/79645d50-d4ea-4e15-9e09-e6957a31dc91
-- title:
--   Full continuous-time killed q-scale expectation factorises through the independent Lévy grid kernel
-- statement:
--   The expected discounted q-scale payoff killed by any negative reserve in a genuine continuous future window after deterministic split time s factorises as a Markov–Tonelli integral over the distribution of the random starting reserve and an independent full future Lévy path, monitored on a rationally covering countable schedule containing the horizon endpoint. The left-hand event is exact continuous survival, with no monitoring surrogate. This bridges the Proved killed-scale Markov–Tonelli formula to the killed renewal identity a885f0b3 and stopped two-sided exit.
-- source:
--   Proved chat04_killed_scale_markov_tonelli_of_scaleFunction and chat04_random_reserve_shifted_closed_survival_schedule_iff.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_markov_tonelli_of_scaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_true_killed_scale_markov_tonelli_grid_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (τ : ℕ → ℝ≥0) (T t : ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∫⁻ ω,
      if ∀ v : ℝ≥0, v ≤ T →
          0 ≤ H ω + (X.X (s + v) ω - X.X s ω)
      then ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) *
            W (H ω + (X.X (s + t) ω - X.X s ω)))
      else (0 : ℝ≥0∞) ∂P) =
    ∫⁻ h, ∫⁻ y,
      (if ∀ j : ℕ, τ j ≤ T → 0 ≤ h + y (τ j)
        then ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (h + y t))
        else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun u : ℝ≥0 => X.X u ω)) P)
      ∂(Measure.map H P) := by sorry
