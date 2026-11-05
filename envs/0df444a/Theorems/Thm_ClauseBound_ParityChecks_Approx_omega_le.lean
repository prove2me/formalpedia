-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Approx_omega_le
-- name    : ClauseBound.ParityChecks.Approx.omega_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:03:59.909776+00:00
-- url     : https://prove2.me/theorems/2852cde1-a513-4574-b469-5e1b45f99b38
-- title:
--   Approx: omega le
-- statement:
--   ω(ξ) ≤ C(|E|, nb + 1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L52-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L52-L53

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
omit [Fintype X] [DecidableEq E]

theorem ClauseBound.ParityChecks.Approx.omega_le (V : X → Finset E) (nb : ℕ) (ξ : X) : omega V nb ξ ≤ (Fintype.card E).choose (nb + 1) := by sorry
