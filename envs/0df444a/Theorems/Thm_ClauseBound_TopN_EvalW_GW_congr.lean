-- Prove2me | Theorems.Thm_ClauseBound_TopN_EvalW_GW_congr
-- name    : ClauseBound.TopN.EvalW.GW_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:44:13.35345+00:00
-- url     : https://prove2.me/theorems/33dfba3c-751f-47ff-8d59-a16036d1c87a
-- title:
--   Eval W: GW congr
-- statement:
--   The weight depends only on the numbers of the layers below R.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean#L166-L169
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean#L166-L169

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_ClauseBound_TopN_EvalW
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.EvalW
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark

theorem ClauseBound.TopN.EvalW.GW_congr (R : ℕ) (ws : List ℤ) (lo hi : List ℕ) (t t' : ℕ → ℕ) (h : ∀ i < R, t i = t' i) : GW R ws lo hi t = GW R ws lo hi t' := by sorry
