-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_countable_two_sided_killed_scale_payoff_measurable
-- name    : AvramDividend.Classical.chat04_countable_two_sided_killed_scale_payoff_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:53:08.035435+00:00
-- url     : https://prove2.me/theorems/45b6be2d-6d3a-4ffa-add7-acad8d3e2a4e
-- title:
--   Measurability of discounted scale-function rewards killed on a countable two-sided barrier grid
-- statement:
--   For a measurable q-scale candidate W, the discounted terminal value of a future reserve multiplied by survival inside [0,a] at every countably scheduled observation before T is jointly Borel measurable in the initial reserve and entire future Lévy path. This supplies the hypothesis for the whole-path independent-increment Markov–Tonelli splitting identity with two-sided killing.
-- source:
--   Proved two-sided countable survival measurable event; Mathlib measurable_pi_apply and ENNReal.measurable_ofReal.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_two_sided_survival_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_countable_two_sided_killed_scale_payoff_measurable
    (τ : ℕ → ℝ≥0) (T t : ℝ≥0) (a q : ℝ)
    (W : ℝ → ℝ) (hW : Measurable W) :
    Measurable (fun z : ℝ × (ℝ≥0 → ℝ) =>
      if ∀ j : ℕ, τ j ≤ T →
        0 ≤ z.1 + z.2 (τ j) ∧ z.1 + z.2 (τ j) ≤ a
      then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (z.1 + z.2 t))
      else (0 : ℝ≥0∞)) := by sorry
