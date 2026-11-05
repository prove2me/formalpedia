-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_StepOne_sum_all
-- name    : ClauseBound.ParityChecks.StepOne.sum_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:31.773483+00:00
-- url     : https://prove2.me/theorems/c3509bcc-5d08-46fb-b469-4b0901774e49
-- title:
--   Step One: sum all
-- statement:
--   Without a bound on the number of marks: the sum over all tuples is the product.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L124-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L124-L136

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

theorem ClauseBound.ParityChecks.StepOne.sum_all {J₁ J₂ : Finset (Fin r)} (hJ : Disjoint J₁ J₂) (A : Fin r → Finset E) :
    ∑ S ∈ Fintype.piFinset (dom A (J₁ ∪ J₂)), ∏ j, fac J₁ J₂ j (S j) = (∏ j ∈ J₁, ev #(A j)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(A j) := by sorry
