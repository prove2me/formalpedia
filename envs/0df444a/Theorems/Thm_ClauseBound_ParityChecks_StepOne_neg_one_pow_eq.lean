-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_StepOne_neg_one_pow_eq
-- name    : ClauseBound.ParityChecks.StepOne.neg_one_pow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:58.44639+00:00
-- url     : https://prove2.me/theorems/5c9afaa3-cbd3-41b5-a846-e4bdd098d9ae
-- title:
--   Step One: neg one pow eq
-- statement:
--   (−1)^q = Σ_i (−2)^i·C(q,i).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L54-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L54-L58

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

theorem ClauseBound.ParityChecks.StepOne.neg_one_pow_eq (q : ℕ) : (-1 : ℤ) ^ q = ∑ i ∈ range (q + 1), (-2 : ℤ) ^ i * q.choose i := by sorry
