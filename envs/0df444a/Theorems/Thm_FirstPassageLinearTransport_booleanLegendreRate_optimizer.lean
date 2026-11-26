-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_booleanLegendreRate_optimizer
-- name    : FirstPassageLinearTransport.booleanLegendreRate_optimizer
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:12:37.482797+00:00
-- url     : https://prove2.me/theorems/2253282b-0c6f-4630-b085-5bc0280e1e9c
-- title:
--   First Passage Linear Transport: boolean Legendre Rate optimizer
-- statement:
--   The optimized Legendre value is exactly binary relative entropy from one
--   half.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L173-L180
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L173-L180

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.booleanLegendreRate_optimizer
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    booleanLegendreRate t (booleanOptimizer t) = binaryBarrierRate t := by sorry
