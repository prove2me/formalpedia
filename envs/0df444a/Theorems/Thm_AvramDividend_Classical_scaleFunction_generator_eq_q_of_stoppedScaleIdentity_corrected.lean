-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_stoppedScaleIdentity_corrected
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_q_of_stoppedScaleIdentity_corrected
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T21:18:34.409798+00:00
-- url     : https://prove2.me/theorems/ea4166b9-f841-4bb4-b788-90c50364a793
-- title:
--   Local Dynkin implication from the corrected stopped scale identity to the generator equation
-- statement:
--   Local stochastic-calculus bridge in the exact product form needed for Lemma 4. Assume W is a q-scale function, is generator-integrable on (0,a), and has the branch smoothness needed for Itô/Dynkin. Assume that for every b>0 and y in [0,b], the corrected killed upward-exit-before-ruin discount expectation multiplied by W(b) equals W(y). This is precisely the stopped q-scale martingale identity, and unlike the ratio form it requires no separate strict-positivity theorem. Localising the stopped Itô/Dynkin identity to a compact interval around an interior x forces the drift (Γ-q)W(x) to vanish.
-- source:
--   Avram, Palmowski and Pistorius (2007), equation (3.6) in product form and proof of Lemma 4, p. 21.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_q_of_stoppedScaleIdentity_corrected
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 W (Ioo 0 a))
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x)
    (hstop : ∀ b y : ℝ, 0 < b → 0 ≤ y → y ≤ b →
      twoSidedExitExpectationCorrected X q b y *
          ENNReal.ofReal (W b) =
        ENNReal.ofReal (W y)) :
    ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
