-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_sum_omega_le
-- name    : ClauseBound.ParityChecks.Start.sum_omega_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:14.331821+00:00
-- url     : https://prove2.me/theorems/77dfbc68-d72c-48dd-b296-a19c54e3331e
-- title:
--   Start: sum omega le
-- statement:
--   Σ_ξ ω(ξ) ≤ |X|·C(|E|, nb + 1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L117-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L117-L123

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
omit [DecidableEq E]

theorem ClauseBound.ParityChecks.Start.sum_omega_le (V : X → Finset E) (nb : ℕ) :
    (∑ ξ, (omega V nb ξ : ℚ)) ≤ ((Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) : ℚ) := by sorry
