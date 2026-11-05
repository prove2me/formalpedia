-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_mem_allTab_getD
-- name    : ClauseBound.Inst.Half.mem_allTab_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:01:23.606495+00:00
-- url     : https://prove2.me/theorems/ba8ca643-64e8-44d0-becb-a0ddf93406e4
-- title:
--   Half: mem all Tab get D
-- statement:
--   Its members are the nonincreasing lists of positive integers with sum E.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L229-L231
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L229-L231

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

theorem ClauseBound.Inst.Half.mem_allTab_getD {W E : ℕ} (h : E ≤ W) {L : List ℕ} :
    L ∈ (allTab W).getD E [] ↔ L.sum = E ∧ (∀ n ∈ L, 1 ≤ n) ∧ L.Pairwise (· ≥ ·) := by sorry
