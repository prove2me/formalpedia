-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_tabOp_rep
-- name    : ClauseBound.Inst.Half.tabOp_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:08.680005+00:00
-- url     : https://prove2.me/theorems/c9cf6310-cd7e-4cb3-a671-5daea26e6d0e
-- title:
--   Half: tab Op rep
-- statement:
--   The table of a[·] holds the matrices of a[r].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L143-L161
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L143-L161

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_Inst_HalfTabSpec
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson

theorem ClauseBound.Inst.Half.tabOp_rep {pad : U} {W : ℕ} {flat : List (List ℕ)} {a : List ℕ} (hW : 1 ≤ W) (hf : FlatOK W flat) (ha : ∀ n ∈ a, n ≤ W)
    (hp : padOp W flat.length a.length ≤ pad.length) : Rep flat (tabOp pad W flat a) (op a) := by sorry
