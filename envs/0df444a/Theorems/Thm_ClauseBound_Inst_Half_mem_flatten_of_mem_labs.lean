-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_mem_flatten_of_mem_labs
-- name    : ClauseBound.Inst.Half.mem_flatten_of_mem_labs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:12.442273+00:00
-- url     : https://prove2.me/theorems/2197b63e-233c-4e68-a193-4149ce6c68c9
-- title:
--   Half: mem flatten of mem labs
-- statement:
--   The partition of a label is listed in the flattened table, and its number j is at most 2h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L114-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L114-L115

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Labs

theorem ClauseBound.Inst.Half.mem_flatten_of_mem_labs {T : PT} {tr : Bool} {h : ℕ} {s : ℤ} {p : ℕ × List ℕ} (hp : p ∈ labs T tr h s) : p.2 ∈ T.flatten ∧ p.1 ≤ 2 * h := by sorry
