-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exp_booleanOptimizer
-- name    : FirstPassageLinearTransport.exp_booleanOptimizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:12:04.375337+00:00
-- url     : https://prove2.me/theorems/a68abbac-d7be-54ad-a386-6a11291f353d
-- title:
--   First Passage Linear Transport: exp boolean Optimizer
-- statement:
--   The First Passage Linear Transport construction uses the exp boolean Optimizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L113-L120
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L113-L120

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.exp_booleanOptimizer
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    Real.exp (booleanOptimizer t) =
      Real.sqrt ((1 / 2 + t) / (1 / 2 - t)) := by sorry
