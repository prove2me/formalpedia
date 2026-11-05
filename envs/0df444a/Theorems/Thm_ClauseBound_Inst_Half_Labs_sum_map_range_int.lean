-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Labs_sum_map_range_int
-- name    : ClauseBound.Inst.Half.Labs.sum_map_range_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:03.333685+00:00
-- url     : https://prove2.me/theorems/043144f3-2c59-4184-b208-a90c91b1c608
-- title:
--   Labs: sum map range int
-- statement:
--   The sum of the values F 0, …, F (n − 1), written with a list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L61-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L61-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Labs
open ClauseBound.Inst.Half.Labs

theorem ClauseBound.Inst.Half.Labs.sum_map_range_int (F : ℕ → ℤ) (n : ℕ) : ((List.range n).map F).sum = ∑ j ∈ range n, F j := by sorry
