-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_term_le
-- name    : ClauseBound.ParityChecks.Start.term_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:16.082283+00:00
-- url     : https://prove2.me/theorems/5406987f-fe0f-44dc-bd21-ea6ab151e3a7
-- title:
--   Start: term le
-- statement:
--   The term of one ξ with v violated clauses when a check begins: the factor ½(1 + (1 − 2p)^v) may
--   be replaced by 5/8.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L105-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L105-L110

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

theorem ClauseBound.ParityChecks.Start.term_le (nb v : ℕ) (hnb : 2 ≤ nb) (c : ℚ) (hc : 0 ≤ c) :
    ((v.choose (nb + 1) : ℕ) : ℚ) * c * (1 / 2 * (1 + (1 - 2 * pr nb) ^ v)) ≤ ((v.choose (nb + 1) : ℕ) : ℚ) * c * (5 / 8) := by sorry
