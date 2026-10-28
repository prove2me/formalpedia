-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_true_killed_scale_markov_tonelli_explicit_schedule
-- name    : AvramDividend.Classical.chat04_true_killed_scale_markov_tonelli_explicit_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:34:24.499675+00:00
-- url     : https://prove2.me/theorems/e9bf74af-64c5-4792-a673-f5eec7a7e255
-- title:
--   Concrete countable Markov kernel for true continuously killed q-scale rewards
-- statement:
--   Construct a single explicit schedule containing all rational relative times and the fixed horizon endpoint, and represent the continuously killed discounted scale-function reward exactly as a nested integral against the independent current-reserve and increment-path laws. This removes abstract coverage assumptions from the Markov–Tonelli reduction used upstream of the two-sided exit identity.
-- source:
--   Proved explicit rational and endpoint schedule and Proved true killed Markov–Tonelli grid-kernel factorisation.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_true_killed_scale_markov_tonelli_grid_kernel
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_true_killed_scale_markov_tonelli_explicit_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (T t : ℝ≥0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ τ : ℕ → ℝ≥0,
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
