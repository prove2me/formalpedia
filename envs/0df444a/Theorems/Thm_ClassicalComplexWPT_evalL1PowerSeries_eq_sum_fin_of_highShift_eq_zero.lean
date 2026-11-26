-- Prove2me | Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_eq_sum_fin_of_highShift_eq_zero
-- name    : ClassicalComplexWPT.evalL1PowerSeries_eq_sum_fin_of_highShift_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:08:09.293806+00:00
-- url     : https://prove2.me/theorems/b7181f59-0f79-4649-89f4-76e06c55f049
-- title:
--   Classical Complex WPT: eval L1 Power Series eq sum fin of high Shift eq zero
-- statement:
--   The Classical Complex WPT construction uses the eval L1 Power Series eq sum fin of high Shift eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1PolynomialEvaluation.lean#L31-L46
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1PolynomialEvaluation.lean#L31-L46

import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.evalL1PowerSeries_eq_sum_fin_of_highShift_eq_zero
    (d : ℕ) (a : L1Sequence) (ha : seqHighShift d a = 0)
    {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries a w = ∑ i : Fin d, a i * w ^ (i : ℕ) := by sorry
