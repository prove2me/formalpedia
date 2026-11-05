-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_StepOne_two_mul_ev
-- name    : ClauseBound.ParityChecks.StepOne.two_mul_ev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:20.175457+00:00
-- url     : https://prove2.me/theorems/5ac8995b-d372-4976-8b1c-7342cf7dd065
-- title:
--   Step One: two mul ev
-- statement:
--   2·[q even] = 1 + (−1)^q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L47-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L47-L51

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

theorem ClauseBound.ParityChecks.StepOne.two_mul_ev (q : ℕ) : 2 * ev q = 1 + (-1) ^ q := by sorry
