-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_RunF_runToC_eq
-- name    : ClauseBound.ParityChecks.RunF.runToC_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:16.543205+00:00
-- url     : https://prove2.me/theorems/6d4af574-8b7e-430f-8df6-b025623ac0b3
-- title:
--   Run F: run To C eq
-- statement:
--   No cut-off is active in the decisions for one check.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L63-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L63-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.RunF
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run
variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)
variable {pad q oA oB}

theorem ClauseBound.ParityChecks.RunF.runToC_eq (hp : lenChk q.m ≤ pad.length) (Ls : List Chk) {e : ℕ} (he : e ≤ q.m) : runToC pad q oA oB Ls e = q.runTo oA oB Ls e := by sorry
