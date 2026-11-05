-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_start
-- name    : ClauseBound.ParityChecks.Start.start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:34.456242+00:00
-- url     : https://prove2.me/theorems/179c974e-0a61-4e11-be4d-bbc8e51519e5
-- title:
--   Start: start
-- statement:
--   At the start the potential is at most 1/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L186-L218
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L186-L218

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

theorem ClauseBound.ParityChecks.Start.start : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r : ℕ), 2 ≤ nb → 1 ≤ r → 1 ≤ Fintype.card E →
    (5 / 8 : ℚ) ^ r * (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) ≤ 1 / 8 → Ups V nb r 0 (fun _ => ∅) univ ≤ 1 / 2 := by sorry
