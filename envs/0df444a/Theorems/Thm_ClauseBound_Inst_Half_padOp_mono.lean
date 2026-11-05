-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_padOp_mono
-- name    : ClauseBound.Inst.Half.padOp_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:02.081542+00:00
-- url     : https://prove2.me/theorems/b3b890e9-2ccb-4203-8703-c8976dfb10de
-- title:
--   Half: pad Op mono
-- statement:
--   The sufficient length of the pad grows with the number of parts.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L138-L140
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L138-L140

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson

theorem ClauseBound.Inst.Half.padOp_mono (W Δ : ℕ) {L L' : ℕ} (h : L ≤ L') : padOp W Δ L ≤ padOp W Δ L' := by sorry
