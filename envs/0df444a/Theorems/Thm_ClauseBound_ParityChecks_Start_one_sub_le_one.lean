-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_one_sub_le_one
-- name    : ClauseBound.ParityChecks.Start.one_sub_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:06.63743+00:00
-- url     : https://prove2.me/theorems/37ea0935-ff78-4607-9a6e-0eb441842da6
-- title:
--   Start: one sub le one
-- statement:
--   1 − 2p ≤ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L46-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L46-L48

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

theorem ClauseBound.ParityChecks.Start.one_sub_le_one {nb : ℕ} (h : 2 ≤ nb) : 1 - 2 * pr nb ≤ 1 := by sorry
