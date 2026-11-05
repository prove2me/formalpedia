-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Approx_abs_prod_ev_cast_le
-- name    : ClauseBound.ParityChecks.Approx.abs_prod_ev_cast_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:34.612205+00:00
-- url     : https://prove2.me/theorems/f619b7a3-c43a-4caf-81e3-fa44827d91d7
-- title:
--   Approx: abs prod ev cast le
-- statement:
--   The same for the rational numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L45-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L45-L48

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

theorem ClauseBound.ParityChecks.Approx.abs_prod_ev_cast_le (s : Finset ℕ) (q : ℕ → ℕ) : |∏ i ∈ s, (ev (q i) : ℚ)| ≤ 1 := by sorry
