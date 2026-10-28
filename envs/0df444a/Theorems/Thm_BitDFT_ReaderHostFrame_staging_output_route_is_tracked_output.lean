-- Prove2me | Theorems.Thm_BitDFT_ReaderHostFrame_staging_output_route_is_tracked_output
-- name    : BitDFT.ReaderHostFrame.staging_output_route_is_tracked_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T18:30:04.689477+00:00
-- url     : https://prove2.me/theorems/c98b2d83-e1c8-4a23-89eb-aea20b512fb9
-- title:
--   The staging output tape is the tracked multiplier caller tape
-- statement:
--   The physical tape on which the operand staging controller writes its output is the tape routed from tape 1 of the tracked multiplier. Thus the staged operand buffer occupies exactly the tracked multiplier caller buffer in the shared host layout. This is the tape-address part of the handoff from operand staging to a multiplier call.
-- source:
--   The routing identity follows from the multiplier bank address formula at the tracked multiplier output tape, whose index is 1.

import Definitions.Def_BitDFT_ReaderHostFrame_WorkSupport_v2
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace BitDFT.ReaderHostFrame
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost

theorem staging_output_route_is_tracked_output (A M H : MultitapeTM) :
    BankedOperandStage.multiplierOutputTape A M H =
      multiplierTapeRoute A M H (tracked M).outTape := by sorry
