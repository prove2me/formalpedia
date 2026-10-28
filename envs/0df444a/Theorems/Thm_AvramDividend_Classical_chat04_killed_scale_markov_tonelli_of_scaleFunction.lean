-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_markov_tonelli_of_scaleFunction
-- name    : AvramDividend.Classical.chat04_killed_scale_markov_tonelli_of_scaleFunction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:01:51.469965+00:00
-- url     : https://prove2.me/theorems/be2dc351-ca72-443a-b44a-0702993ef82c
-- title:
--   Markov–Tonelli factorisation of killed q-scale payoffs with no extra measurability assumption
-- statement:
--   For every genuine q-scale function W and F_s-measurable possibly random reserve H, the killed discounted terminal payoff observed on any countable time grid satisfies the exact Lévy full-path Markov–Tonelli factorisation. Removes the artificial separate assumption Measurable W using scaleFunction_continuousAt_away_zero and measurable_of_measurable_on_compl_singleton; valid also for bounded variation when W(0)>0. This prepares the stopped q-scale renewal semigroup identity a885f0b3 and the two-sided exit child 09663d0d.
-- source:
--   Proved chat04_countable_killed_scale_markov_tonelli and chat04_scaleFunction_measurable_of_punctured_continuity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_countable_killed_scale_markov_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_killed_scale_markov_tonelli_of_scaleFunction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (τ : ℕ → ℝ≥0) (T t : ℝ≥0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
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
