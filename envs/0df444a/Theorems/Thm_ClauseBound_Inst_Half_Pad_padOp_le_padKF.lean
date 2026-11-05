-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Pad_padOp_le_padKF
-- name    : ClauseBound.Inst.Half.Pad.padOp_le_padKF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:46.086871+00:00
-- url     : https://prove2.me/theorems/1c070a69-f094-4fd4-81a6-c8fb4ef3a2e0
-- title:
--   Pad: pad Op le pad KF
-- statement:
--   The pad for the table of a[·] is shorter than the pad for the tables of the parts of a^μ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L49-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L49-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfVal
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Definitions.Def_ClauseBound_Inst_HalfPad
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
open ClauseBound.Inst.Half.Pad

theorem ClauseBound.Inst.Half.Pad.padOp_le_padKF (W Δ h s L : ℕ) : padOp W Δ L ≤ padKF W Δ h s L := by sorry
