-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Pad_padOp_le_padLen
-- name    : ClauseBound.Inst.Half.Pad.padOp_le_padLen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:59.336215+00:00
-- url     : https://prove2.me/theorems/62948faf-f1de-472e-900d-40dba6908f8c
-- title:
--   Pad: pad Op le pad Len
-- statement:
--   The pad of length padLen h suffices for the table of the operators (t^μ)[·], μ a partition of h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L96-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L96-L98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfVal
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Definitions.Def_ClauseBound_Inst_HalfPad
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
open ClauseBound.Inst.Half.Pad

theorem ClauseBound.Inst.Half.Pad.padOp_le_padLen {h : ℕ} {μ : List ℕ} (hμ : μ ∈ (allTab (4 * h)).flatten) (hs : μ.sum = h) :
    padOp (4 * h) (allTab (4 * h)).flatten.length μ.length ≤ padLen h := by sorry
