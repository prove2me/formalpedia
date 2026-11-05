-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_stp_of_ne
-- name    : CircuitLowerBound.Oracle.stp_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:02:11.185086+00:00
-- url     : https://prove2.me/theorems/5421dd28-edac-4c4b-9575-642c057245ac
-- title:
--   Oracle: stp of ne
-- statement:
--   A step at a label other than `ask` runs the statement at that label.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L229-L232
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L229-L232

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_TM_Run
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Machine
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable (M : TM2ComputableAux Bool Bool)
variable {M}

theorem CircuitLowerBound.Oracle.stp_of_ne (O : Lang) {l : Λ' M} (hl : l ≠ .inr .ask) (v : σ' M) (S : ∀ k, List (Γ' M k)) :
    stp M O ⟨some l, v, S⟩ = some (TM2.stepAux (prog M l) v S) := by sorry
