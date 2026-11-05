-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_one_sub_nonneg
-- name    : ClauseBound.ParityChecks.Start.one_sub_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:05.015545+00:00
-- url     : https://prove2.me/theorems/e0beb0c0-290e-4d41-a2ba-c15b0af661a2
-- title:
--   Start: one sub nonneg
-- statement:
--   0 ≤ 1 − 2p.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L40-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L40-L43

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

theorem ClauseBound.ParityChecks.Start.one_sub_nonneg {nb : ℕ} (h : 2 ≤ nb) : 0 ≤ 1 - 2 * pr nb := by sorry
