-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_RunF_runChecks_shape
-- name    : ClauseBound.ParityChecks.RunF.runChecks_shape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:58.074194+00:00
-- url     : https://prove2.me/theorems/94f9e6cd-3de8-4c13-8859-1e2ef8005520
-- title:
--   Run F: run Checks shape
-- statement:
--   The first j checks are j lists with short words.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L75-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L75-L83

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

theorem ClauseBound.ParityChecks.RunF.runChecks_shape (j : ℕ) : (q.runChecks oA oB j).length = j ∧ ∀ L ∈ q.runChecks oA oB j, len L ≤ lenChk q.m := by sorry
