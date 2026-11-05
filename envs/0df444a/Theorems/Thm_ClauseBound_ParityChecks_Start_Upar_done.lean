-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_Upar_done
-- name    : ClauseBound.ParityChecks.Start.Upar_done
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:17.282233+00:00
-- url     : https://prove2.me/theorems/00ec858b-1595-4fe0-bb65-4ba07e0d2cc1
-- title:
--   Start: Upar done
-- statement:
--   Υ_par when all clauses are decided for check j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L140-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L140-L147

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
omit [Fintype E]

theorem ClauseBound.ParityChecks.Start.Upar_done (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) :
    Upar V nb r j Λ ∅ = (5 / 8) ^ (r - 1 - j) * ∑ ξ, (omega V nb ξ : ℚ) * ∏ j' ∈ range (j + 1), (ev #(Λ j' ∩ V ξ) : ℚ) := by sorry
