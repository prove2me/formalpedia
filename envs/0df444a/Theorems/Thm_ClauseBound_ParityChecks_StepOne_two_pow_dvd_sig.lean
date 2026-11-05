-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_StepOne_two_pow_dvd_sig
-- name    : ClauseBound.ParityChecks.StepOne.two_pow_dvd_sig
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:32.270162+00:00
-- url     : https://prove2.me/theorems/ed0badc7-2b63-4aac-84eb-febcee0b606e
-- title:
--   Step One: two pow dvd sig
-- statement:
--   σ_i is divisible by 2^(i−1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L139-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L139-L143

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

theorem ClauseBound.ParityChecks.StepOne.two_pow_dvd_sig (i : ℕ) : (2 : ℤ) ^ (i - 1) ∣ sig i := by sorry
