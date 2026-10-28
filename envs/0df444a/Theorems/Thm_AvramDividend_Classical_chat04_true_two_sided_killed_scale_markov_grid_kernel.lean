-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_true_two_sided_killed_scale_markov_grid_kernel
-- name    : AvramDividend.Classical.chat04_true_two_sided_killed_scale_markov_grid_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:10:53.225837+00:00
-- url     : https://prove2.me/theorems/e8090da5-8b2a-4a0e-8b57-5cc9aa0fff91
-- title:
--   Full continuously two-sided-killed scale-function expectation factorises through a countable Lévy Markov kernel
-- statement:
--   The genuinely continuous-time event that a shifted Lévy reserve with any adapted initial capital H remains within [0,a] for every time through T can be substituted by a rationally covering countable observation grid. The discounted terminal q-scale reward under that event satisfies an exact full-path independent-increment Markov–Tonelli factorisation, without separate measurability assumptions on W. This bridges the two-sided stopping-time and semigroup verification workstreams.
-- source:
--   Proved exact two-sided survival schedule equivalence, countable two-sided killed scale Markov–Tonelli, and scale-function Borel measurability.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_countable_two_sided_killed_scale_markov_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_two_sided_survival_schedule_iff

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_true_two_sided_killed_scale_markov_grid_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (a : ℝ) (τ : ℕ → ℝ≥0) (T t : ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
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
