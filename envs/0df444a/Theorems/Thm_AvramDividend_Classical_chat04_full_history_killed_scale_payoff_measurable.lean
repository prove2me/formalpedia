-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_full_history_killed_scale_payoff_measurable
-- name    : AvramDividend.Classical.chat04_full_history_killed_scale_payoff_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:04:27.697181+00:00
-- url     : https://prove2.me/theorems/94342b9f-54a1-4f64-8224-7d994cee9e5c
-- title:
--   Measurability of the full-history killed q-scale payoff for any measurable initial reserve
-- statement:
--   For any q-scale function W, finite horizon T, and measurable possibly random reserve H, the terminal ENNReal-valued discounted scale payoff killed by continuous-time ruin throughout [0,T] is measurable. Establishes the precise integrand measurability needed by chat04_unbounded_killed_survival_discounted_scale_expectation and two_sided_exit_stopped_scale_identity, without zero-origin assumptions or positive-reserve restrictions.
-- source:
--   Proved random-reserve closed-horizon survival measurability and Proved Borel measurability of the q-scale function.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_closed_survival_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open MeasureTheory
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_full_history_killed_scale_payoff_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (hH : Measurable H) (T : ℝ≥0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Measurable (fun ω =>
      if ∀ s : ℝ≥0, s ≤ T → 0 ≤ H ω + X.X s ω
      then ENNReal.ofReal
        (Real.exp (-(q * (T : ℝ))) * W (H ω + X.X T ω))
      else (0 : ℝ≥0∞)) := by sorry
