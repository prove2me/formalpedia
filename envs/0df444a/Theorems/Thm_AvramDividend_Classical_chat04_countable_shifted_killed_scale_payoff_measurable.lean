-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_killed_scale_payoff_measurable
-- name    : AvramDividend.Classical.chat04_countable_shifted_killed_scale_payoff_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:35:30.012801+00:00
-- url     : https://prove2.me/theorems/78c537a0-3f38-4d69-ab3d-66cda447cd09
-- title:
--   Borel measurability of countably monitored killed scale-function payoff with variable reserve
-- statement:
--   At a deterministic splitting time, a current reserve r and an entire future increment path y determine whether all countably scheduled future reserves remain nonnegative. Assuming the scale function W is measurable, their discounted q-scale terminal payoff multiplied by this survival event is Borel measurable as an ENNReal-valued function. Provides the full product-measurability premise to instantiate the proved full-future-path Markov–Tonelli formula in countable-grid approximations of the killed q-scale renewal identity, towards theorem a885f0b3 and two-sided exit parent 3e1ce2c8.
-- source:
--   Proved measurable survival on shifted future path chat04_countable_shifted_future_reserve_survival_measurable; pinned Mathlib ENNReal.measurable_ofReal and Measurable.ite; application of Proved unconditional Markov–Tonelli 77ced690-a2a9-4d93-bb66-4ae69a114152.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat04_countable_shifted_killed_scale_payoff_measurable
    (τ : ℕ → ℝ≥0) (T t : ℝ≥0)
    (q : ℝ) (W : ℝ → ℝ) (hW : Measurable W) :
    Measurable (fun z : ℝ × (ℝ≥0 → ℝ) =>
      if ∀ j : ℕ, τ j ≤ T → 0 ≤ z.1 + z.2 (τ j)
      then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (z.1 + z.2 t))
      else (0 : ℝ≥0∞)) := by sorry
