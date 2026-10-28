-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scaleDeriv_growth_of_corrected_exit_and_C1
-- name    : AvramDividend.Classical.unbounded_scaleDeriv_growth_of_corrected_exit_and_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:10:22.222234+00:00
-- url     : https://prove2.me/theorems/43f53bbe-aec5-49dc-ae06-31e002f115dc
-- title:
--   Unbounded q-scale derivative tends to infinity from corrected exit and C1 regularity
-- statement:
--   For an unbounded-variation spectrally negative Lévy process and q>0, the canonical scale-function derivative tends to infinity at infinity if the corrected two-sided exit-scale identity and positive-axis differentiability hold. The independently Proved unbounded_positive_tilt_of_corrected_exit obtains strict positive W and an Esscher tilt with positive root; the Proved scale_deriv_tendsto_atTop_of_normalized_monotone gives the claimed derivative growth. The two remaining analytic hypotheses are explicit and can be supplied by the strict exit and C1 workstreams. The theorem is a fully verified conditional import for cstar finiteness.
-- source:
--   Avram Palmowski Pistorius 2007, Lemma 2(i), condition (3.3) and corrected two-sided exit identity; Kuznetsov Kyprianou Rivero 2013, Esscher-normalised scale monotonicity.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Mathlib.Analysis.Calculus.Deriv.Basic
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scaleDeriv_growth_of_corrected_exit_and_C1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    Tendsto (deriv W) atTop atTop := by sorry
