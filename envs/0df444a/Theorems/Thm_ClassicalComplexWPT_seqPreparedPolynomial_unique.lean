-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqPreparedPolynomial_unique
-- name    : ClassicalComplexWPT.seqPreparedPolynomial_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:12.420258+00:00
-- url     : https://prove2.me/theorems/bded7560-bf4a-55d9-8ee5-3f29f9ac5397
-- title:
--   Classical Complex WPT: seq Prepared Polynomial unique
-- statement:
--   Abstract uniqueness of a prepared polynomial.  Here `p` and `p'` are the
--   low-degree tails of two monic degree-`d` polynomials, while `v` is the
--   coefficient sequence of the ratio of their analytic units.  The displayed
--   identity says `(w^d + p) = v * (w^d + p')` in weighted coefficients.
--
--   This theorem is deliberately independent of how the coefficient sequences
--   were extracted from analytic germs.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L305-L328
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L305-L328

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

theorem ClassicalComplexWPT.seqPreparedPolynomial_unique (d : ℕ) (p p' v : L1Coeff ℕ)
    (hp' : ‖p'‖ < 1)
    (hpLow : seqHighShift d p = 0)
    (hp'Low : seqHighShift d p' = 0)
    (hfactor :
      seqLowShift d constantOneSeq + p =
        seqLowShift d v + convolution v p') :
    p = p' ∧ v = constantOneSeq := by sorry
