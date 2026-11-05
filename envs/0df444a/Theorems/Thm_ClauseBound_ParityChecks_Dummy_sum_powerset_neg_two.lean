-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Dummy_sum_powerset_neg_two
-- name    : ClauseBound.ParityChecks.Dummy.sum_powerset_neg_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:09.054206+00:00
-- url     : https://prove2.me/theorems/e6bdd98a-ea50-4f64-9169-878e8c3ca63f
-- title:
--   Dummy: sum powerset neg two
-- statement:
--   Σ_{S ⊆ T} (−2)^|S| = (−1)^|T|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean#L35-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean#L35-L39

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

theorem ClauseBound.ParityChecks.Dummy.sum_powerset_neg_two {α : Type} (T : Finset α) : ∑ S ∈ T.powerset, (-2 : ℤ) ^ #S = (-1) ^ #T := by sorry
