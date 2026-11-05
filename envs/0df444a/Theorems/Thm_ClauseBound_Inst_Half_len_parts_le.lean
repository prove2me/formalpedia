-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_len_parts_le
-- name    : ClauseBound.Inst.Half.len_parts_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:17:43.878201+00:00
-- url     : https://prove2.me/theorems/72fb01db-034d-46cc-8059-e5ad8c8ce0a9
-- title:
--   Half: len parts le
-- statement:
--   The word of a list of positive integers with sum E has length at most 7E + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L276-L284
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L276-L284

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset

theorem ClauseBound.Inst.Half.len_parts_le (L : List ℕ) (h : ∀ n ∈ L, 1 ≤ n) : len L ≤ 7 * L.sum + 2 := by sorry
