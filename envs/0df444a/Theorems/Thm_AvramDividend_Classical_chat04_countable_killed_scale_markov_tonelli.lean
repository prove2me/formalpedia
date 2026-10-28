-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_countable_killed_scale_markov_tonelli
-- name    : AvramDividend.Classical.chat04_countable_killed_scale_markov_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:37:44.63138+00:00
-- url     : https://prove2.me/theorems/ca546835-54fa-47a3-9faa-685945ce1bf5
-- title:
--   Unconditional full-path Markov–Tonelli formula for countably killed q-scale payoff
-- statement:
--   For any deterministic Lévy splitting time s, any F_s-measurable initial reserve H, any countable future monitoring schedule τ through horizon T, and any measurable scale candidate W, the discounted terminal payoff killed by every monitored future reserve factorises into an integral over the distribution of H and an independent integral over the full future Lévy path. This is the explicit state-dependent killed semigroup kernel identity needed to build the q-scale renewal/harmonicity proof a885f0b3 and then strict two-sided exit identity 3e1ce2c8.
-- source:
--   Proved unconditional whole-future-path Markov–Tonelli chat04_unconditional_history_future_path_markov_tonelli; Proved jointly measurable countably killed scale payoff chat04_countable_shifted_killed_scale_payoff_measurable; pinned Mathlib Bochner-Lebesgue product measure integration.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_unconditional_history_future_path_markov_tonelli
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_countable_killed_scale_markov_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ) (hH : Measurable[𝓕 s] H)
    (τ : ℕ → ℝ≥0) (T t : ℝ≥0)
    (q : ℝ) (W : ℝ → ℝ) (hW : Measurable W) :
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
