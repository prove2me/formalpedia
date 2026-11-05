-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Labs_mem_flatten_of_mem_getD
-- name    : ClauseBound.Inst.Half.Labs.mem_flatten_of_mem_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:43:36.731664+00:00
-- url     : https://prove2.me/theorems/367375da-4024-478c-9293-687688042e92
-- title:
--   Labs: mem flatten of mem get D
-- statement:
--   A member of an entry of a table is a member of the flattened table.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L74-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L74-L79

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
open ClauseBound.Inst.Half.Labs

theorem ClauseBound.Inst.Half.Labs.mem_flatten_of_mem_getD {γ : Type} {T : List (List γ)} {i : ℕ} {L : γ} (h : L ∈ T.getD i []) : L ∈ T.flatten := by sorry
