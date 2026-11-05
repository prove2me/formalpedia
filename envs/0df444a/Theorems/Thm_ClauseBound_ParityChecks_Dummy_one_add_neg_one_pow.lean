-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Dummy_one_add_neg_one_pow
-- name    : ClauseBound.ParityChecks.Dummy.one_add_neg_one_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:14.425635+00:00
-- url     : https://prove2.me/theorems/24730eab-7f52-439f-ae95-adcc3962a723
-- title:
--   Dummy: one add neg one pow
-- statement:
--   1 + (−1)^q = 2·[q even].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean#L67-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean#L67-L71

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

theorem ClauseBound.ParityChecks.Dummy.one_add_neg_one_pow (q : ℕ) : (-1 : ℤ) ^ q + 1 = 2 * ev q := by sorry
