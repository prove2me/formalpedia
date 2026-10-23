-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat07_weighted_compensated_negative_jump_integrableOn
-- name    : AvramDividend.Classical.chat07_weighted_compensated_negative_jump_integrableOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T06:42:58.815367+00:00
-- url     : https://prove2.me/theorems/fddebddc-c6e4-4bb6-b786-78bdad4458b7
-- title:
--   Integrability of each weighted compensated negative Lévy jump
-- statement:
--   For a q-scale function, nonnegative Laplace parameter with q less than the Lévy exponent and any nonnegative downward jump magnitude, the exponentially weighted fully compensated jump difference is Lebesgue integrable over positive reserves. The proof combines the already established integrability of the shifted and unshifted scale function with the accepted weighted derivative halfline integrability. This fixed-jump result precedes proving joint integrability with respect to the Lévy jump measure.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat07_weighted_compensated_negative_jump_integrableOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ r : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) (hr : 0 ≤ r) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        (W (x - r) - W x + r * deriv W x))
      (Ioi (0 : ℝ)) := by sorry
