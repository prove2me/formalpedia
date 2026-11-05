-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Pad_length_flatten_allTab_four
-- name    : ClauseBound.Inst.Half.Pad.length_flatten_allTab_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:51.533584+00:00
-- url     : https://prove2.me/theorems/bb65c20b-e4ff-478e-8daf-081216ed8275
-- title:
--   Pad: length flatten all Tab four
-- statement:
--   The flattened table of the partitions of 0, …, 4h has deltaF h members.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L45-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L45-L46

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

theorem ClauseBound.Inst.Half.Pad.length_flatten_allTab_four (h : ℕ) : (allTab (4 * h)).flatten.length = deltaF h := by sorry
