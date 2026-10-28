-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_markov_tonelli_with_explicit_grid
-- name    : AvramDividend.Classical.chat04_killed_scale_markov_tonelli_with_explicit_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:08:57.878575+00:00
-- url     : https://prove2.me/theorems/2789be9f-3c99-47db-a9d0-9d90c6dbbb35
-- title:
--   Concrete rational-grid Markov–Tonelli factorisation for killed q-scale rewards
-- statement:
--   For every Lévy process, F_s-measurable random reserve H and genuine scale function W, construct a specific countable monitoring schedule containing each rational time k/n and the terminal horizon, and establish the exact nested Markov–Tonelli kernel for the discounted scale-function reward killed on that grid. Combines already Proved schedule coverage and killed-scale Markov independence, removing existential scheduling work upstream of the continuously killed semigroup.
-- source:
--   Proved explicit shifted killed survival schedule and Proved killed scale Markov–Tonelli theorem.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_markov_tonelli_of_scaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_killed_scale_markov_tonelli_with_explicit_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (T t : ℝ≥0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ τ : ℕ → ℝ≥0,
      (∀ n : ℕ, 0 < n → ∀ k : ℕ,
        ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ∧
      (∃ j : ℕ, τ j = T) ∧
      (∫⁻ ω,
        if ∀ j : ℕ, τ j ≤ T →
          0 ≤ H ω + (X.X (s + τ j) ω - X.X s ω)
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
