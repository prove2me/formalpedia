-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_countable_two_sided_killed_scale_markov_tonelli
-- name    : AvramDividend.Classical.chat04_countable_two_sided_killed_scale_markov_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:57:44.647547+00:00
-- url     : https://prove2.me/theorems/4b261ebd-adf2-476b-afd6-6bd0dfb1f45a
-- title:
--   Exact Markov–Tonelli splitting for a Lévy q-scale reward killed at two barriers on a countable schedule
-- statement:
--   For any deterministic splitting time s, an adapted possibly random starting reserve H, and a full future Lévy increment path, the discounted terminal scale reward conditioned on every scheduled reserve remaining inside [0,a] factorises into an iterated integral over the marginal reserve distribution and independent whole-future-path law. Assumes the candidate W measurable, which is automatic for genuine scale functions.
-- source:
--   Proved unconditional-history full-future-path Markov–Tonelli and two-sided countable killed-payoff measurability.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_unconditional_history_future_path_markov_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_countable_two_sided_killed_scale_payoff_measurable

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_countable_two_sided_killed_scale_markov_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (τ : ℕ → ℝ≥0) (T t : ℝ≥0)
    (a q : ℝ) (W : ℝ → ℝ) (hW : Measurable W) :
    (∫⁻ ω,
      if ∀ j : ℕ, τ j ≤ T →
        0 ≤ H ω + (X.X (s + τ j) ω - X.X s ω) ∧
        H ω + (X.X (s + τ j) ω - X.X s ω) ≤ a
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
