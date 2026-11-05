-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_RunF_runTo_shape
-- name    : ClauseBound.ParityChecks.RunF.runTo_shape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:48.331205+00:00
-- url     : https://prove2.me/theorems/5dc6654f-2e80-4048-bb8a-bad07c93455f
-- title:
--   Run F: run To shape
-- statement:
--   After e decisions the check is a list of at most e clauses, all below e.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L41-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/RunF.lean#L41-L52

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

theorem ClauseBound.ParityChecks.RunF.runTo_shape (Ls : List Chk) (e : ℕ) : (q.runTo oA oB Ls e).length ≤ e ∧ ∀ x ∈ q.runTo oA oB Ls e, x < e := by sorry
