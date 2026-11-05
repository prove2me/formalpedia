-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Labs_sum_range_getElem
-- name    : ClauseBound.Inst.Half.Labs.sum_range_getElem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:57.450803+00:00
-- url     : https://prove2.me/theorems/1705583e-a13c-4ad3-95c0-7ee8ea496bd9
-- title:
--   Labs: sum range get Elem
-- statement:
--   A sum over the positions of a list, continued by zeros.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L35-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L35-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open ClauseBound.Inst.Half.Labs

theorem ClauseBound.Inst.Half.Labs.sum_range_getElem {β : Type} (F : β → ℤ) (L : List β) : ∀ M, L.length ≤ M → ∑ j ∈ range M, (L[j]?).elim 0 F = (L.map F).sum := by sorry
