-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_scale_derivative_right_continuous_extension
-- name    : AvramDividend.Classical.gaussian_scale_derivative_right_continuous_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:16:00.745671+00:00
-- url     : https://prove2.me/theorems/0bf82051-7a77-441c-9923-8dc1b03899ac
-- title:
--   Correct right-continuous Gaussian scale-derivative extension at zero
-- statement:
--   The Gaussian scale derivative is continuous at positive reserves and has the right-hand limit 2/sigma squared at the origin. Patching its value at zero to exactly this positive right limit therefore produces a function continuous on all nonnegative reserves. It is essential to use this extension rather than the ordinary Lean deriv W 0, which is zero by the previously proved local-minimum theorem. The result composes two Proved Gaussian results and a Proved general positive-to-closed-halfline continuity gluing lemma.
-- source:
--   Proved scaleDeriv_continuous_of_gaussian, corrected scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma, and causal_continuousOn_Ici_of_positive_limit.

import Mathlib.Topology.NhdsWithin
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
import Theorems.Thm_AvramDividend_Classical_causal_continuousOn_Ici_of_positive_limit
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace AvramDividend.Classical
/-- The Gaussian scale derivative admits its correct right-continuous endpoint extension. -/
theorem gaussian_scale_derivative_right_continuous_extension
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (hzero : W 0 = 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x) :
    ContinuousOn (fun x : ℝ => if x = 0 then 2 / X.σ ^ 2 else deriv W x)
      (Ici (0 : ℝ)) := by
  sorry
end AvramDividend.Classical
