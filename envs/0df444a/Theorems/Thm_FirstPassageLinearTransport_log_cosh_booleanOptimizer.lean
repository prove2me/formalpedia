-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_log_cosh_booleanOptimizer
-- name    : FirstPassageLinearTransport.log_cosh_booleanOptimizer
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:12:13.215812+00:00
-- url     : https://prove2.me/theorems/76849a30-f9b5-5755-a5da-6fd3376409d3
-- title:
--   First Passage Linear Transport: log cosh boolean Optimizer
-- statement:
--   The First Passage Linear Transport construction uses the log cosh boolean Optimizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L155-L169
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L155-L169

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.log_cosh_booleanOptimizer
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    Real.log (Real.cosh (booleanOptimizer t)) =
      -Real.log 2 -
        (Real.log (1 / 2 + t) + Real.log (1 / 2 - t)) / 2 := by sorry
