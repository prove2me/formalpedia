-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Dummy_neg_two_pow_modEq
-- name    : ClauseBound.ParityChecks.Dummy.neg_two_pow_modEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:13.536221+00:00
-- url     : https://prove2.me/theorems/4b765ed0-6c58-4734-a49e-5263fa7add2f
-- title:
--   Dummy: neg two pow mod Eq
-- statement:
--   A power of −2 with an exponent above M vanishes modulo 2^{M+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean#L102-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean#L102-L106

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

theorem ClauseBound.ParityChecks.Dummy.neg_two_pow_modEq {M k : ℕ} : (-2 : ℤ) ^ k ≡ (if k ≤ M then (-2 : ℤ) ^ k else 0) [ZMOD 2 ^ (M + 1)] := by sorry
