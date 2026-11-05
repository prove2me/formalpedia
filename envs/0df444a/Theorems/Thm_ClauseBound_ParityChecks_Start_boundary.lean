-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_boundary
-- name    : ClauseBound.ParityChecks.Start.boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:36.808322+00:00
-- url     : https://prove2.me/theorems/7b4362a7-64a5-41d5-b66f-9cb14f3b0453
-- title:
--   Start: boundary
-- statement:
--   From one check to the next the potential does not grow.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L221-L237
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L221-L237

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset

theorem ClauseBound.ParityChecks.Start.boundary : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E),
    2 ≤ nb → IsState r j Λ ∅ → j + 1 < r → Ups V nb r (j + 1) Λ univ ≤ Ups V nb r j Λ ∅ := by sorry
