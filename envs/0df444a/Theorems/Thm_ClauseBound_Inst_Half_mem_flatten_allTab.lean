-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_mem_flatten_allTab
-- name    : ClauseBound.Inst.Half.mem_flatten_allTab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:54:06.879495+00:00
-- url     : https://prove2.me/theorems/6dff0be1-ce0b-4736-b71d-224df33a3282
-- title:
--   Half: mem flatten all Tab
-- statement:
--   The members of the flattened table are the nonincreasing lists of positive integers with sum at
--   most W.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L250-L261
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L250-L261

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

theorem ClauseBound.Inst.Half.mem_flatten_allTab {W : ℕ} {L : List ℕ} :
    L ∈ (allTab W).flatten ↔ L.sum ≤ W ∧ (∀ n ∈ L, 1 ≤ n) ∧ L.Pairwise (· ≥ ·) := by sorry
