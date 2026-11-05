-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_StepOne_prod_mul_prod
-- name    : ClauseBound.ParityChecks.StepOne.prod_mul_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:05:07.745197+00:00
-- url     : https://prove2.me/theorems/5d2f8783-92c0-4966-9425-7c14763e1995
-- title:
--   Step One: prod mul prod
-- statement:
--   Two products over disjoint sets of checks as one product over all checks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L110-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L110-L118

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

theorem ClauseBound.ParityChecks.StepOne.prod_mul_prod {J₁ J₂ : Finset (Fin r)} (hJ : Disjoint J₁ J₂) (a b : Fin r → ℤ) :
    (∏ j ∈ J₁, a j) * ∏ j ∈ J₂, b j = ∏ j, if j ∈ J₁ then a j else if j ∈ J₂ then b j else 1 := by sorry
