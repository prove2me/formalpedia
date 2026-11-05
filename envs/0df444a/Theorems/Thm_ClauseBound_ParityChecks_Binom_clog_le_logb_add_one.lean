-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Binom_clog_le_logb_add_one
-- name    : ClauseBound.ParityChecks.Binom.clog_le_logb_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:03:30.20799+00:00
-- url     : https://prove2.me/theorems/b7cf340e-59ab-4085-b7a6-1155365a4c59
-- title:
--   Binom: clog le logb add one
-- statement:
--   Rounding a binary logarithm up costs at most one bit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Binom.lean#L33-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Binom.lean#L33-L38

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
open ClauseBound.ParityChecks.Binom

theorem ClauseBound.ParityChecks.Binom.clog_le_logb_add_one {x : ℕ} (hx : 1 ≤ x) : (Nat.clog 2 x : ℝ) ≤ Real.logb 2 x + 1 := by sorry
