-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_StepOne_dvd_term
-- name    : ClauseBound.ParityChecks.StepOne.dvd_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:36.17205+00:00
-- url     : https://prove2.me/theorems/a3bfc867-7bfb-4fa3-b761-972f413083bd
-- title:
--   Step One: dvd term
-- statement:
--   The term of a tuple with more than ν − 1 + |J₁| marks is divisible by 2^ν.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L151-L174
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L151-L174

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks
variable {E : Type} {r : ℕ}

theorem ClauseBound.ParityChecks.StepOne.dvd_term {J₁ J₂ : Finset (Fin r)} (A : Fin r → Finset E) {S : Fin r → Finset E} (hS : S ∈ Fintype.piFinset (dom A (J₁ ∪ J₂))) {ν : ℕ}
    (hν : ν + #J₁ ≤ ∑ j, #(S j)) : (2 : ℤ) ^ ν ∣ ∏ j, fac J₁ J₂ j (S j) := by sorry
