-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_Upar_fresh_le
-- name    : ClauseBound.ParityChecks.Start.Upar_fresh_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:05:23.138224+00:00
-- url     : https://prove2.me/theorems/b8fa5623-c8a1-4707-a6f3-e397929f83c4
-- title:
--   Start: Upar fresh le
-- statement:
--   Υ_par when check j begins.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L126-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L126-L136

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
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]

theorem ClauseBound.ParityChecks.Start.Upar_fresh_le (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (hnb : 2 ≤ nb) (hΛ : Λ j = ∅) :
    Upar V nb r j Λ univ ≤
      (5 / 8) ^ (r - 1 - j) * (5 / 8 * ∑ ξ, (omega V nb ξ : ℚ) * ∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ)) := by sorry
