-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Val_pad_allTab
-- name    : ClauseBound.Inst.Half.Val.pad_allTab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:46.792717+00:00
-- url     : https://prove2.me/theorems/8328a0b2-ca62-43cc-adbd-f3d23d90085c
-- title:
--   Val: pad all Tab
-- statement:
--   A pad of length `padLen h` suffices for the table of all partitions of 0, …, 4h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfVal.lean#L64-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfVal.lean#L64-L70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfVal
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open ClauseBound.Inst.Half.Val

theorem ClauseBound.Inst.Half.Val.pad_allTab {h : ℕ} {pad : U} (hp : padLen h ≤ pad.length) :
    (7 * (4 * h) + 10) * ∑ E ∈ range (4 * h + 1), Partitions.p E ≤ pad.length := by sorry
