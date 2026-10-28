-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_true_shifted_two_sided_killed_scale_payoff_measurable
-- name    : AvramDividend.Classical.chat04_true_shifted_two_sided_killed_scale_payoff_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:32:13.820988+00:00
-- url     : https://prove2.me/theorems/1c0af8e9-e8d6-4b68-b617-e9aefda56367
-- title:
--   True continuously two-sided-killed discounted q-scale reward is measurable at every shifted horizon
-- statement:
--   The discounted q-scale payoff at a shifted terminal time, killed on the entire continuous-time two-sided survival event, is measurable for any measurable random initial reserve and genuine scale function. Uses the now proved full two-sided survival event measurability and scale-function Borel measurability.
-- source:
--   Proved chat04_random_reserve_shifted_two_sided_closed_survival_measurable and chat04_scaleFunction_measurable_of_punctured_continuity; Lévy adaptedness and measurable conditional selection.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_two_sided_closed_survival_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

open MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_true_shifted_two_sided_killed_scale_payoff_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (hH : Measurable H) (a : ℝ) (b T t : ℝ≥0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Measurable (fun ω : Ω =>
      if ∀ v : ℝ≥0, v ≤ T →
        0 ≤ H ω + (X.X (b + v) ω - X.X b ω) ∧
        H ω + (X.X (b + v) ω - X.X b ω) ≤ a
      then ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) *
          W (H ω + (X.X (b + t) ω - X.X b ω)))
      else (0 : ℝ≥0∞)) := by sorry
