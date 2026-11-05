-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_foldl_roundT
-- name    : ClauseBound.Inst.Half.foldl_roundT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:54:26.451201+00:00
-- url     : https://prove2.me/theorems/e271ac67-dd04-4abb-bdfd-f35ff5cccf62
-- title:
--   Half: foldl round T
-- statement:
--   The first j rounds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L217-L222
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L217-L222

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset

theorem ClauseBound.Inst.Half.foldl_roundT (W j : ℕ) : (List.range j).foldl (fun old k => roundT W (k + 1) old) (initT W) = tabK W j := by sorry
