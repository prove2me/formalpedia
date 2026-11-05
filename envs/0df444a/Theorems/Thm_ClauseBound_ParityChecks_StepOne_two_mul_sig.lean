-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_StepOne_two_mul_sig
-- name    : ClauseBound.ParityChecks.StepOne.two_mul_sig
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:20.283498+00:00
-- url     : https://prove2.me/theorems/7f298518-8652-47f0-99e4-747a479eedad
-- title:
--   Step One: two mul sig
-- statement:
--   2σ_i = (−2)^i + [i = 0].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L38-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L38-L44

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

theorem ClauseBound.ParityChecks.StepOne.two_mul_sig (i : ℕ) : 2 * sig i = (-2) ^ i + if i = 0 then 1 else 0 := by sorry
