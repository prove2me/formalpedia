-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_scale_derivative_continuous_corrected_on_nonnegative
-- name    : AvramDividend.Classical.gaussian_scale_derivative_continuous_corrected_on_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:32:26.298084+00:00
-- url     : https://prove2.me/theorems/be32f53e-92d3-4fbc-b0aa-725d808d717e
-- title:
--   Corrected Gaussian scale derivative is continuous through zero without side hypotheses
-- statement:
--   Without extra boundary or differentiability assumptions, the corrected derivative extension f(0)=2/sigma squared, f(x)=deriv W(x) for x>0, is continuous on [0,infinity) for every q>0 spectrally negative Lévy scale function with strictly positive Gaussian coefficient. Use already-Proved Gaussian scale W(0)=0 and C1 smoothing on positive levels, then the Proved corrected right-continuous extension theorem. This does not confuse the two-sided derivative deriv W 0, which is zero, with the positive-side Gaussian limit. Its prerequisite is now canonically Proved, and this publication revision pins the explicit endpoint topology import.
-- source:
--   Composition of Proved scaleFunction_zero_origin_gaussian_without_standing, scaleFunction_contDiff_one_gaussian_without_standing, and corrected right-continuous Gaussian derivative extension.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Mathlib.Topology.NhdsWithin
import Theorems.Thm_AvramDividend_Classical_gaussian_scale_derivative_right_continuous_extension
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace AvramDividend.Classical
/-- The positive Gaussian scale derivative has a canonical right-continuous nonnegative-time extension. -/
theorem gaussian_scale_derivative_continuous_corrected_on_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ContinuousOn (fun x : ℝ => if x = 0 then 2 / X.σ ^ 2 else deriv W x)
      (Ici (0 : ℝ)) := by
  sorry
end AvramDividend.Classical
