-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_RunF_runC_eq
-- name    : ClauseBound.ParityChecks.RunF.runC_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:45.784493+00:00
-- url     : https://prove2.me/theorems/e427b85e-99b3-4079-9b5e-172d51fce47f
-- title:
--   Run F: run C eq
-- statement:
--   No cut-off is active in the whole choice.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L91-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L91-L102

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

theorem ClauseBound.ParityChecks.RunF.runC_eq (hp : q.r * (lenChk q.m + 2) + 2 ≤ pad.length) (hp' : lenChk q.m ≤ pad.length) : runC pad q oA oB = q.run oA oB := by sorry
