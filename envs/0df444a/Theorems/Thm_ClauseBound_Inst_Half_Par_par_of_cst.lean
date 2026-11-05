-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Par_par_of_cst
-- name    : ClauseBound.Inst.Half.Par.par_of_cst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:58.60597+00:00
-- url     : https://prove2.me/theorems/0f3ec631-847f-44e0-bf57-e0ceb9cf76bf
-- title:
--   Par: par of cst
-- statement:
--   If c₀ and c are large enough at every length, then `halfF c₀ c` has the parameters (1/√2, c).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPar.lean#L56-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPar.lean#L56-L76

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_ClauseBound_Inst_HalfPar
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Part ClauseBound.Inst.Rec
open ClauseBound.Inst.Half.Par

theorem ClauseBound.Inst.Half.Par.par_of_cst (hS : StSpec) {c₀ c : ℕ} (hC : ∀ lam : ℕ, 1 ≤ lam → Cst c₀ c lam) : ClauseBound.Gen.Par (halfF c₀ c) (1 / Real.sqrt 2) c := by sorry
