-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_StepOne_two_pow_dvd_neg_two_pow
-- name    : ClauseBound.ParityChecks.StepOne.two_pow_dvd_neg_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:33.719118+00:00
-- url     : https://prove2.me/theorems/35b80a00-cfe9-4188-a9ac-b22b61b1f899
-- title:
--   Step One: two pow dvd neg two pow
-- statement:
--   (−2)^i is divisible by 2^i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L146-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L146-L148

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

theorem ClauseBound.ParityChecks.StepOne.two_pow_dvd_neg_two_pow (i : ℕ) : (2 : ℤ) ^ i ∣ (-2) ^ i := by sorry
