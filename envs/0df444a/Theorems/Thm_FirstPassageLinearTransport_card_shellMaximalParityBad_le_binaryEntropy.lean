-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_shellMaximalParityBad_le_binaryEntropy
-- name    : FirstPassageLinearTransport.card_shellMaximalParityBad_le_binaryEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:13:02.480678+00:00
-- url     : https://prove2.me/theorems/df3400ec-800c-42b7-9519-84106bab4e5a
-- title:
--   First Passage Linear Transport: card shell Maximal Parity Bad le binary Entropy
-- statement:
--   Shellwise entropy-sharp maximal-parity exceptional count.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L193-L208
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/EntropyBarrier.lean#L193-L208

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.card_shellMaximalParityBad_le_binaryEntropy
    (t : ℝ) (M : ℕ) (ht0 : 0 ≤ t) (ht1 : t < 1 / 2) :
    ((shellMaximalParityBad M (t * M)).card : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) * binaryBarrierRate t)) := by sorry
