-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_continuous_on_positive_bv
-- name    : AvramDividend.Classical.vcstar_deriv_continuous_on_positive_bv
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T23:19:22.184162+00:00
-- url     : https://prove2.me/theorems/869721ac-142c-4cf4-9bd7-6c97ce2cf307
-- title:
--   Continuity of the first derivative of the BV candidate at and across the positive optimal barrier
-- statement:
--   For a bounded-variation spectrally negative Lévy process satisfying the standing condition, establish continuity of the derivative of v_{c*} on all positive reserves, including across the positive minimising barrier c*. Below c*, v'=W'/W'(c*), whose continuity follows from regularity of the scale function. Above c* the derivative is one. The crucial value matching at the barrier follows from the minimisation/smooth-fit property, so the two branches glue continuously. This is the substantive remaining analytic obligation for the global C1 regularity required by the unrestricted verification lemma.
-- source:
--   Avram, Palmowski and Pistorius (2007), condition (3.3), Lemma 3(i) and Theorem 2, BV smooth fit across c*. Relationship to Mathlib contDiffOn_one_of_differentiable_continuous_deriv_Ioi.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem vcstar_deriv_continuous_on_positive_bv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) :
    ContinuousOn (deriv (vcstar W)) (Ioi 0) := by
  sorry
end AvramDividend.Classical
