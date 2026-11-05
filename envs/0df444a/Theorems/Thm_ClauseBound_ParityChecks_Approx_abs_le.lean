-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Approx_abs_le
-- name    : ClauseBound.ParityChecks.Approx.abs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:47.789964+00:00
-- url     : https://prove2.me/theorems/618e38d5-7b6c-46fc-adab-649f10411710
-- title:
--   Approx: abs le
-- statement:
--   A and B_i are small.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L114-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L114-L148

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic
import Definitions.Def_ClauseBound_ParityChecks_Approx
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Approx
open Finset _root_.ParityChecks
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]

theorem ClauseBound.ParityChecks.Approx.abs_le (V : X → Finset E) (nb i j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) :
    |Aint V nb j Λ| ≤ (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) ∧
      |Bint V nb i j Λ D| ≤ (Fintype.card X * (Fintype.card E).choose (nb + 1) * (Fintype.card E).choose i : ℕ) := by sorry
