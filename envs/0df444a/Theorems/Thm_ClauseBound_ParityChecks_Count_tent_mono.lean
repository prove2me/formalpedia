-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Count_tent_mono
-- name    : ClauseBound.ParityChecks.Count.tent_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:41.429814+00:00
-- url     : https://prove2.me/theorems/69cf481f-a4a6-43e3-91c3-e95f7060e9c9
-- title:
--   Count: tent mono
-- statement:
--   The bounds for states that are tried pass to smaller checks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean#L83-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Count.lean#L83-L92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_ClauseBound_ParityChecks_Count
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Count
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Eval ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW _root_.ParityChecks

theorem ClauseBound.ParityChecks.Count.tent_mono {q : Par} {Λ Λ' : ℕ → Finset (Fin q.m)} (h : ∀ j, Λ' j ⊆ Λ j) (hT : Tent q Λ) : Tent q Λ' := by sorry
