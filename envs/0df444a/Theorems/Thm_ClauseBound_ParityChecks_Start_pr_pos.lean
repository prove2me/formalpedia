-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_pr_pos
-- name    : ClauseBound.ParityChecks.Start.pr_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:05:20.865002+00:00
-- url     : https://prove2.me/theorems/250e01a6-8feb-4dc9-8c2f-c483c2aabe0c
-- title:
--   Start: pr pos
-- statement:
--   p > 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L35-L37

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

theorem ClauseBound.ParityChecks.Start.pr_pos {nb : ℕ} (h : 2 ≤ nb) : 0 < pr nb := by sorry
