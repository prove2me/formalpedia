-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_logb_choose_le
-- name    : ClauseBound.ParityChecks.logb_choose_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:06.96305+00:00
-- url     : https://prove2.me/theorems/cfe1cfd1-2300-4c66-ae04-fcb918b4fc7b
-- title:
--   Parity Checks: logb choose le
-- statement:
--   log₂ C(t, μ) ≤ μ'·max{1, log₂(3t/μ')} for μ ≤ μ', μ' ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Binom.lean#L53-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Binom.lean#L53-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Binom
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Binom

theorem ClauseBound.ParityChecks.logb_choose_le {t μ μ' : ℕ} (h : μ ≤ μ') (h1 : 1 ≤ μ') :
    Real.logb 2 (t.choose μ) ≤ μ' * max 1 (Real.logb 2 (3 * t / μ')) := by sorry
