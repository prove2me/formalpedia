-- Prove2me | Theorems.Thm_BitDFT_coordinate_head_frame_irrelevance
-- name    : BitDFT.coordinate_head_frame_irrelevance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T15:43:11.088494+00:00
-- url     : https://prove2.me/theorems/6db026df-d6e0-4325-9d53-6bffe739f90c
-- title:
--   Coordinate-reader head is irrelevant to staging frames
-- statement:
--   Let a controller source record `[sign, high] ++ low` on its coordinate tape. The staging entry frame overwrites the coordinate tape head with its own scan position, and the final copied-coordinate frame also sets that head explicitly. Therefore changing only the incoming coordinate-tape head leaves both frames identical. This lets an extracted reader record be staged regardless of where the reader left its head.
-- source:
--   Direct frame extensionality for the published banked operand-stage support definitions. The result isolates the head-position interface between an exact coordinate reader and the operand staging controller.

import Definitions.Def_BitDFT_MachineSequence
import Definitions.Def_BitDFT_OperandStage
import Definitions.Def_BitDFT_BankedOperandStageProofSupport
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open IntMul BitDFT.OperandStage BitDFT.BankedOperandStageProofSupport BitDFT.MachineSequence

theorem BitDFT.coordinate_head_frame_irrelevance {N : MultitapeTM}
    (coord dim out : Fin N.k) (hc : coord ≠ N.inTape) (hd : dim ≠ N.inTape)
    (ho : out ≠ N.inTape) (hcd : coord ≠ dim) (hco : coord ≠ out) (hdo : dim ≠ out)
    (base : (control N coord dim out hc hd ho hcd hco hdo).machine.Cfg)
    (source : List Bool) (outBits : List N.Sym) (sourceHead outHead head' : ℕ) :
    initialStageFrame coord dim out hc hd ho hcd hco hdo
        ⟨base.state, base.cells, Function.update base.head coord head'⟩ source =
      initialStageFrame coord dim out hc hd ho hcd hco hdo base source ∧
    coordinateCopyFrame coord dim out hc hd ho hcd hco hdo
        ⟨base.state, base.cells, Function.update base.head coord head'⟩
        source outBits sourceHead outHead =
      coordinateCopyFrame coord dim out hc hd ho hcd hco hdo base
        source outBits sourceHead outHead := by sorry
