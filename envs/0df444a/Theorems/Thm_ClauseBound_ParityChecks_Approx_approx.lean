-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Approx_approx
-- name    : ClauseBound.ParityChecks.Approx.approx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:01.364375+00:00
-- url     : https://prove2.me/theorems/93fac22f-75f7-4d70-ac62-ed1be8b5a26e
-- title:
--   Approx: approx
-- statement:
--   The error of the truncated series carries over to the potential.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L63-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L63-L94

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

theorem ClauseBound.ParityChecks.Approx.approx (V : X → Finset E) (nb r i₀ j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) (ε : ℚ)
    (hε : ∀ u ≤ Fintype.card E, |(1 - 2 * pr nb) ^ u - ∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * (u.choose i : ℚ)| ≤ ε) :
    |tUpar V nb r i₀ j Λ D - Upar V nb r j Λ D| ≤ 1 / 2 * ε * (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) := by sorry
