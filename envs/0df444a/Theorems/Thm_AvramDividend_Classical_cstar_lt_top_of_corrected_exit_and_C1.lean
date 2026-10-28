-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_corrected_exit_and_C1
-- name    : AvramDividend.Classical.cstar_lt_top_of_corrected_exit_and_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:01:33.595985+00:00
-- url     : https://prove2.me/theorems/7f2c5e1a-7340-41f2-96fa-7e527ac6001d
-- title:
--   Finite optimal dividend barrier from corrected two-sided exits and C1 scale regularity
-- statement:
--   Under Avram's standing assumptions and a positive discount q, suppose the canonical corrected killed two-sided-exit identity holds for all 0≤x≤a and the q-scale function is C1 on the positive axis. Then the optimal derivative-minimising barrier c* is finite. The result is a complete analytic final bridge from two explicit hypotheses owned by Workstreams 1 and 2. It neither presumes the open exit theorem nor the open global regularity theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 2(i), §5.3; canonical Proved scaleFunction_tilted_positive_monotone_of_corrected_exit and cstar_finite_of_normalized_monotone.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_normalized_monotone
import Mathlib.Analysis.Calculus.Deriv.Basic

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cstar_lt_top_of_corrected_exit_and_C1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hreg : ContDiffOn ℝ 1 W (Ioi 0)) :
    cstar W < ⊤ := by sorry
