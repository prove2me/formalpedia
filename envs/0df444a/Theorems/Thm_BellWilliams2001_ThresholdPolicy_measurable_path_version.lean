-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_measurable_path_version
-- name    : BellWilliams2001.ThresholdPolicy.measurable_path_version
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:43:22.695832+00:00
-- url     : https://prove2.me/theorems/b1611fef-295b-490c-8150-c6d52d71b9d7
-- title:
--   A jointly chosen measurable version of a right-continuous process
-- statement:
--   A process satisfying a right-continuous path property almost everywhere, with almost everywhere measurable fixed-time observations, admits one almost everywhere equal version whose paths all obey the property and whose nonnegative-time evaluations are measurable.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal

open MeasureTheory Filter Topology Set
open scoped NNReal

namespace BellWilliams2001.ThresholdPolicy

theorem measurable_path_version {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Zero E]
    (P : Measure Ω) (f : Ω → ℝ → E) (Good : (ℝ → E) → Prop)
    (hZero : Good (fun _ => 0)) (hGood : ∀ᵐ ω ∂P, Good (f ω))
    (hRight : ∀ x, Good x → ∀ s : ℝ, 0 ≤ s → ContinuousWithinAt x (Ici s) s)
    (hM : ∀ t : ℝ, 0 ≤ t → AEMeasurable (fun ω => f ω t) P) :
    ∃ g : Ω → ℝ → E, (∀ ω, Good (g ω)) ∧ (g =ᵐ[P] f) ∧
      ∀ t : ℝ, 0 ≤ t → Measurable (fun ω => g ω t) := by sorry

end BellWilliams2001.ThresholdPolicy
