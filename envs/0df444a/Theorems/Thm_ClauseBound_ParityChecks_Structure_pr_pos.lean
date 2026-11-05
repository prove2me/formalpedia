-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Structure_pr_pos
-- name    : ClauseBound.ParityChecks.Structure.pr_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:40.139849+00:00
-- url     : https://prove2.me/theorems/5ff50554-34ec-42ed-9e0c-5e0b8e7ab731
-- title:
--   Structure: pr pos
-- statement:
--   p = 1/nb is positive.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Structure.lean#L32-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Structure.lean#L32-L35

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

theorem ClauseBound.ParityChecks.Structure.pr_pos {nb : ℕ} (h : 2 ≤ nb) : 0 < pr nb := by sorry
