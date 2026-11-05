-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Val_mem_flatten_of_mem_getD
-- name    : ClauseBound.Inst.Half.Val.mem_flatten_of_mem_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:26.000029+00:00
-- url     : https://prove2.me/theorems/45e04cf0-8423-4961-9724-de6d45ba2e4b
-- title:
--   Val: mem flatten of mem get D
-- statement:
--   A member of an entry of a table is a member of the flattened table.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfVal.lean#L44-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfVal.lean#L44-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfVal
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset
open ClauseBound.Inst.Half.Val

theorem ClauseBound.Inst.Half.Val.mem_flatten_of_mem_getD {γ : Type} {T : List (List γ)} {n : ℕ} {L : γ} (h : L ∈ T.getD n []) : L ∈ T.flatten := by sorry
