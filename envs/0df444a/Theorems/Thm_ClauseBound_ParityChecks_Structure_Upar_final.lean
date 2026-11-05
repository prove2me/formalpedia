-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Structure_Upar_final
-- name    : ClauseBound.ParityChecks.Structure.Upar_final
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:45.549104+00:00
-- url     : https://prove2.me/theorems/c3a22e2c-2b23-45fe-92e4-8f79773bf3e3
-- title:
--   Structure: Upar final
-- statement:
--   In the final state the first term of the potential is the integer Σ_ξ ω(ξ)·∏_{j' < r} [|V_j'(ξ)|
--   even].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Structure.lean#L92-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Structure.lean#L92-L98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Structure
set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Structure
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype E]

theorem ClauseBound.ParityChecks.Structure.Upar_final (V : X → Finset E) (nb r : ℕ) (Λ : ℕ → Finset E) :
    Upar V nb (r + 1) r Λ ∅ = ((∑ ξ, (omega V nb ξ : ℤ) * ∏ j' ∈ range (r + 1), ev #(Λ j' ∩ V ξ) : ℤ) : ℚ) := by sorry
