-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_RunF_len_runTo_le
-- name    : ClauseBound.ParityChecks.RunF.len_runTo_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:48:47.709461+00:00
-- url     : https://prove2.me/theorems/6713f810-e0e6-4d42-8d1c-0af70d8b54f6
-- title:
--   Run F: len run To le
-- statement:
--   The word of a check is short.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L55-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L55-L60

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

theorem ClauseBound.ParityChecks.RunF.len_runTo_le (Ls : List Chk) {e : ℕ} (he : e ≤ q.m) : len (q.runTo oA oB Ls e) ≤ lenChk q.m := by sorry
