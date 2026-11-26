-- Prove2me | Theorems.Thm_ClassicalComplexWPT_convolution_monomialSeq
-- name    : ClassicalComplexWPT.convolution_monomialSeq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:09:11.383412+00:00
-- url     : https://prove2.me/theorems/f3c3deee-59ba-57b7-b659-36506d8f3612
-- title:
--   Classical Complex WPT: convolution monomial Seq
-- statement:
--   Convolution with the degree-`d` monomial inserts `d` leading zero
--   coefficients.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L71-L101
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationSequences.lean#L71-L101

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 5000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.convolution_monomialSeq (q : OriginSeq) (d : ℕ) :
    convolution q (monomialSeq d) = seqLowShift d q := by sorry
