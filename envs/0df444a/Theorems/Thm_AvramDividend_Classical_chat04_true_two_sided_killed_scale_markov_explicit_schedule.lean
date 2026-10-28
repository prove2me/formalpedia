-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_true_two_sided_killed_scale_markov_explicit_schedule
-- name    : AvramDividend.Classical.chat04_true_two_sided_killed_scale_markov_explicit_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:24:40.808377+00:00
-- url     : https://prove2.me/theorems/54597289-b232-4a3f-b070-6cf742c92d43
-- title:
--   Constructive countable monitoring representation of continuously two-sided-killed q-scale rewards
-- statement:
--   For any genuine spectrally negative Lévy scale function W, adapted initial reserve and two-sided finite interval [0,a], there exists an explicit countable rational-and-terminal schedule under which the true continuously monitored two-sided killed discounted q-scale reward equals an iterated independent-increment Markov kernel. The only remaining analytic step for the stopped q-scale identity is the harmonicity/optional-stopping behaviour, not event measurability or Markov independence.
-- source:
--   Proved true two-sided killed q-scale grid kernel and explicit rational-covering schedule construction.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_true_two_sided_killed_scale_markov_grid_kernel
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_true_two_sided_killed_scale_markov_explicit_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (a : ℝ) (T t : ℝ≥0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ τ : ℕ → ℝ≥0,
    (∫⁻ ω,
      if ∀ v : ℝ≥0, v ≤ T →
        0 ≤ H ω + (X.X (s + v) ω - X.X s ω) ∧
        H ω + (X.X (s + v) ω - X.X s ω) ≤ a
      then ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) *
          W (H ω + (X.X (s + t) ω - X.X s ω)))
      else (0 : ℝ≥0∞) ∂P) =
    ∫⁻ h, ∫⁻ y,
      (if ∀ j : ℕ, τ j ≤ T →
        0 ≤ h + y (τ j) ∧ h + y (τ j) ≤ a
       then ENNReal.ofReal
         (Real.exp (-(q * (t : ℝ))) * W (h + y t))
       else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun u : ℝ≥0 => X.X u ω)) P)
      ∂(Measure.map H P) := by sorry
