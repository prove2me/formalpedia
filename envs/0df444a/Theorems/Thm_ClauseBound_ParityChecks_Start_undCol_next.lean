-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_undCol_next
-- name    : ClauseBound.ParityChecks.Start.undCol_next
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:59:38.356602+00:00
-- url     : https://prove2.me/theorems/1f26c4f2-600e-4bd9-aeb6-82f70739643c
-- title:
--   Start: und Col next
-- statement:
--   The checks not yet decided, clause by clause: the same before and after the passage to the next
--   check.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L160-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L160-L164

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

theorem ClauseBound.ParityChecks.Start.undCol_next (r j : ℕ) (h : j + 1 < r) : undCol r (j + 1) (univ : Finset E) = undCol r j (∅ : Finset E) := by sorry
