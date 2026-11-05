-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_RunF_len_runChecks_le
-- name    : ClauseBound.ParityChecks.RunF.len_runChecks_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:19.855211+00:00
-- url     : https://prove2.me/theorems/45ac761d-b746-4491-b6c7-63bcd0cd9d08
-- title:
--   Run F: len run Checks le
-- statement:
--   The word of the list of the first j ≤ r checks is short.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L86-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L86-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.RunF
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run
variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)
variable {pad q oA oB}

theorem ClauseBound.ParityChecks.RunF.len_runChecks_le {j : ℕ} (hj : j ≤ q.r) : len (q.runChecks oA oB j) ≤ q.r * (lenChk q.m + 2) + 2 := by sorry
