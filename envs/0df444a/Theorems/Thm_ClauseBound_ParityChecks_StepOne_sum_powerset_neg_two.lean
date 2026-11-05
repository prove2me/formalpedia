-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_StepOne_sum_powerset_neg_two
-- name    : ClauseBound.ParityChecks.StepOne.sum_powerset_neg_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:25.958198+00:00
-- url     : https://prove2.me/theorems/b97ac3c6-843d-4fe9-9eb3-fdde6640a7cf
-- title:
--   Step One: sum powerset neg two
-- statement:
--   The sum of (−2)^|s| over the subsets s of a set.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L78-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L78-L80

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

theorem ClauseBound.ParityChecks.StepOne.sum_powerset_neg_two {E : Type} (A : Finset E) : ∑ s ∈ A.powerset, (-2 : ℤ) ^ #s = (-1) ^ #A := by sorry
