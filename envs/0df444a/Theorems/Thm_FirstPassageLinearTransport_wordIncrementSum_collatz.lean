-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_collatz
-- name    : FirstPassageLinearTransport.wordIncrementSum_collatz
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:28:19.728545+00:00
-- url     : https://prove2.me/theorems/919117bc-086d-540c-888e-b22a019867e2
-- title:
--   First Passage Linear Transport: word Increment Sum collatz
-- statement:
--   The increment sum depends only on the number of true bits.  This is the
--   lattice identity used to reduce every middle-block terminal interval to at
--   most one binomial atom.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L941-L956
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L941-L956

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.wordIncrementSum_collatz
    {r : ℕ} (v : Fin r → Bool) :
    wordIncrementSum collatzLogIncrement v =
      ((boolSupport v).card : ℝ) * Real.log 3 - (r : ℝ) * Real.log 2 := by sorry
