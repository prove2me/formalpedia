-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Pad_length_flatten_allTab
-- name    : ClauseBound.Inst.Half.Pad.length_flatten_allTab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:32.04665+00:00
-- url     : https://prove2.me/theorems/ec4e6525-c7c8-4138-8255-6c401a243ba6
-- title:
--   Pad: length flatten all Tab
-- statement:
--   The flattened table has Σ_{E ≤ W} p(E) members.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L33-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L33-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfVal
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_ClauseBound_Inst_HalfTabKF
import Definitions.Def_ClauseBound_Inst_HalfTabBot
import Definitions.Def_ClauseBound_Inst_HalfPad
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
open ClauseBound.Inst.Half.Pad

theorem ClauseBound.Inst.Half.Pad.length_flatten_allTab (W : ℕ) : (allTab W).flatten.length = ∑ E ∈ Finset.range (W + 1), p E := by sorry
