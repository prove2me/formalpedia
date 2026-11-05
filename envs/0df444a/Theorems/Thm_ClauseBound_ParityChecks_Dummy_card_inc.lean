-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Dummy_card_inc
-- name    : ClauseBound.ParityChecks.Dummy.card_inc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:56.995566+00:00
-- url     : https://prove2.me/theorems/45e49f6d-5289-477d-977e-187ae57ce64b
-- title:
--   Dummy: card inc
-- statement:
--   The number of violated incidences, check by check.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean#L43-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean#L43-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Dummy
set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Dummy
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype X]

theorem ClauseBound.ParityChecks.Dummy.card_inc (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (ξ : X) (y : Fin r → Bool) :
    #(inc V r Λ J₁ J₂ ξ y) = ∑ j : Fin r, if (j ∈ J₁ ∧ y j = true) ∨ j ∈ J₂ then #(Λ j ∩ V ξ) else 0 := by sorry
