-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Val_mem_labs
-- name    : ClauseBound.Inst.Half.Val.mem_labs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:38:30.169755+00:00
-- url     : https://prove2.me/theorems/f013ec21-6e9f-4d35-8abe-41a7c3937f59
-- title:
--   Val: mem labs
-- statement:
--   A pair (j, τ) of the list of labels has j ≤ 2h and a listed τ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfVal.lean#L52-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfVal.lean#L52-L57

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

theorem ClauseBound.Inst.Half.Val.mem_labs {T : PT} {tr : Bool} {h : ℕ} {s : ℤ} {p : ℕ × List ℕ} (hp : p ∈ labs T tr h s) : p.1 ≤ 2 * h ∧ p.2 ∈ T.flatten := by sorry
