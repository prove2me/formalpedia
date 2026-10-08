-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_twoSidedExitIdentity_corrected
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_of_twoSidedExitIdentity_corrected
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T21:17:09.118721+00:00
-- url     : https://prove2.me/theorems/92be16b9-8414-42bb-a205-0ad705107025
-- title:
--   Local Dynkin implication from the corrected two-sided exit identity to the generator equation
-- statement:
--   Local stochastic-calculus bridge using the corrected killed two-sided-exit expectation. Assume W is a q-scale function, lies in the generator domain throughout (0,a), and has the branch smoothness required for Itô/Dynkin. Assume for every b>0 and y in [0,b] that the corrected discounted upward-exit-before-ruin expectation equals W(y)/W(b). Then (Γ-q)W=0 throughout (0,a). Fix an interior point, stop on a compact subinterval, use the exit identity to show the stopped expectation equals the initial value, apply Itô/Dynkin and localise to identify the drift at the starting point.
-- source:
--   Avram, Palmowski and Pistorius (2007), equation (3.6) and proof of Lemma 4, p. 21.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_of_twoSidedExitIdentity_corrected
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 W (Ioo 0 a))
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x)
    (hexit : ∀ b y : ℝ, 0 < b → 0 ≤ y → y ≤ b →
      twoSidedExitExpectationCorrected X q b y =
        ENNReal.ofReal (W y / W b)) :
    ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
