-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Approx_abs_prod_ev_le
-- name    : ClauseBound.ParityChecks.Approx.abs_prod_ev_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:03:54.814609+00:00
-- url     : https://prove2.me/theorems/42933bf3-d132-47ce-957d-f56f7d2a1b28
-- title:
--   Approx: abs prod ev le
-- statement:
--   A product of numbers [q even] has absolute value at most 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L40-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L40-L42

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

theorem ClauseBound.ParityChecks.Approx.abs_prod_ev_le (s : Finset ℕ) (q : ℕ → ℕ) : |∏ i ∈ s, ev (q i)| ≤ 1 := by sorry
