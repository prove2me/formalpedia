-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_five_eighths
-- name    : ClauseBound.ParityChecks.Start.five_eighths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:05:22.916781+00:00
-- url     : https://prove2.me/theorems/31b0e6e5-792e-44ce-bd44-a70cec5d3312
-- title:
--   Start: five eighths
-- statement:
--   ½(1 + (1 − 2p)^v) < 5/8 for v > nb.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L91-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L91-L101

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

theorem ClauseBound.ParityChecks.Start.five_eighths : ∀ nb v : ℕ, 2 ≤ nb → nb < v → 1 / 2 * (1 + (1 - 2 * pr nb) ^ v) < 5 / 8 := by sorry
