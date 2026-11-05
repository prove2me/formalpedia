-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_tabOp_cons
-- name    : ClauseBound.Inst.Half.tabOp_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:32.999205+00:00
-- url     : https://prove2.me/theorems/f28989df-aff2-4949-a99a-870baabb30ee
-- title:
--   Half: tab Op cons
-- statement:
--   The table of (n :: a)[·] is made from that of a[·] by one round.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L133-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfTabSpec.lean#L133-L135

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

theorem ClauseBound.Inst.Half.tabOp_cons (pad : U) (W : ℕ) (flat : List (List ℕ)) (n : ℕ) (a : List ℕ) :
    tabOp pad W flat (n :: a) = cap pad [] (tab flat (nopE W n flat (tabOp pad W flat a))) := by sorry
