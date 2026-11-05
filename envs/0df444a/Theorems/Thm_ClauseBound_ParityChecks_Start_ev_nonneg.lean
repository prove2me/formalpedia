-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Start_ev_nonneg
-- name    : ClauseBound.ParityChecks.Start.ev_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:05:17.958953+00:00
-- url     : https://prove2.me/theorems/73d39c8c-1b88-479a-bb18-f2bb3d52e384
-- title:
--   Start: ev nonneg
-- statement:
--   [q even] ≥ 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L58-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Start.lean#L58-L59

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

theorem ClauseBound.ParityChecks.Start.ev_nonneg (q : ℕ) : (0 : ℚ) ≤ (ev q : ℚ) := by sorry
