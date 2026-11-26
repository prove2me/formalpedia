-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqDivision_zero_remainder_unique
-- name    : ClassicalComplexWPT.seqDivision_zero_remainder_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:42.099372+00:00
-- url     : https://prove2.me/theorems/b1b115de-af66-4ae8-8bcd-f9b08a26b1d2
-- title:
--   Classical Complex WPT: seq Division zero remainder unique
-- statement:
--   Specialized two-factorization principle used in preparation uniqueness:
--   if one decomposition has zero remainder and another has a low-degree
--   remainder, then the quotients agree and that remainder vanishes.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L283-L296
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L283-L296

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

theorem ClassicalComplexWPT.seqDivision_zero_remainder_unique (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f q q' r : L1Coeff ℕ)
    (hfac : f = seqLowShift d q + convolution q p)
    (hfac' : f = seqLowShift d q' + convolution q' p + r)
    (hr : seqHighShift d r = 0) :
    q = q' ∧ r = 0 := by sorry
