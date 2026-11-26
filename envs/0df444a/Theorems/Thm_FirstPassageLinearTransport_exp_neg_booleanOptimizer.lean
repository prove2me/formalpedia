-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exp_neg_booleanOptimizer
-- name    : FirstPassageLinearTransport.exp_neg_booleanOptimizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:12:06.493904+00:00
-- url     : https://prove2.me/theorems/37598634-1967-554e-a081-99099537950c
-- title:
--   First Passage Linear Transport: exp neg boolean Optimizer
-- statement:
--   The First Passage Linear Transport construction uses the exp neg boolean Optimizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L122-L132
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L122-L132

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.exp_neg_booleanOptimizer
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    Real.exp (-booleanOptimizer t) =
      Real.sqrt ((1 / 2 - t) / (1 / 2 + t)) := by sorry
