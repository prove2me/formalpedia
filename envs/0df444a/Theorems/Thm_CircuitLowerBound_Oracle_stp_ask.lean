-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_stp_ask
-- name    : CircuitLowerBound.Oracle.stp_ask
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:44:06.852747+00:00
-- url     : https://prove2.me/theorems/6ac929a1-3e09-47c5-9dcf-9a11d8b364d3
-- title:
--   Oracle: stp ask
-- statement:
--   A step at `ask`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L236-L239
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L236-L239

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
open Classical

theorem CircuitLowerBound.Oracle.stp_ask (O : Lang) (v : σ' M) (S : ∀ k, List (Γ' M k)) :
    stp M O ⟨some (.inr .ask), v, S⟩ =
      some ⟨some (if O ((S (.inl M.tm.k₁)).map M.outputAlphabet) then .inr .yes else .inr .no), v, Function.update S (.inl M.tm.k₁) []⟩ := by sorry
