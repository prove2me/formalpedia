-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqPreparedPolynomial_unique_of_eventually_eval
-- name    : ClassicalComplexWPT.seqPreparedPolynomial_unique_of_eventually_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:32.624696+00:00
-- url     : https://prove2.me/theorems/2ed4912c-24b3-4bf7-ace2-94359ff766eb
-- title:
--   Classical Complex WPT: seq Prepared Polynomial unique of eventually eval
-- statement:
--   Evaluation-level form of `seqPreparedPolynomial_unique`.  This avoids any
--   need for a multivariable uniqueness theorem: after fixing the base point, the
--   ordinary one-variable uniqueness theorem identifies the two `ℓ¹` coefficient
--   sequences.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L334-L348
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L334-L348

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_Basic
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.seqPreparedPolynomial_unique_of_eventually_eval (d : ℕ)
    (p p' v : L1Coeff ℕ)
    (hp' : ‖p'‖ < 1)
    (hpLow : seqHighShift d p = 0)
    (hp'Low : seqHighShift d p' = 0)
    (heval :
      (fun w ↦ evalL1PowerSeries (seqLowShift d constantOneSeq + p) w) =ᶠ[nhds 0]
        (fun w ↦ evalL1PowerSeries
          (seqLowShift d v + convolution v p') w)) :
    p = p' ∧ v = constantOneSeq := by sorry
