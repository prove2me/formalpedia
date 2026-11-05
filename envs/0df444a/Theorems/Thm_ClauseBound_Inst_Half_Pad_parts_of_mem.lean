-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Pad_parts_of_mem
-- name    : ClauseBound.Inst.Half.Pad.parts_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:52:40.68071+00:00
-- url     : https://prove2.me/theorems/bb82f016-6828-414a-bdef-73d22e7bd3d6
-- title:
--   Pad: parts of mem
-- statement:
--   A partition μ of h in the list: at most h parts, each at most 4h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L82-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPad.lean#L82-L87

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

theorem ClauseBound.Inst.Half.Pad.parts_of_mem {h : ℕ} {μ : List ℕ} (hμ : μ ∈ (allTab (4 * h)).flatten) (hs : μ.sum = h) :
    μ.length ≤ h ∧ ∀ n ∈ μ, n ≤ 4 * h := by sorry
