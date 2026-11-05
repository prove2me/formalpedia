-- Prove2me | Theorems.Thm_ClauseBound_TopN_EvalW_GW_mul_sgnP
-- name    : ClauseBound.TopN.EvalW.GW_mul_sgnP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:44:25.540951+00:00
-- url     : https://prove2.me/theorems/09a05012-342c-416d-b500-1e6333b05134
-- title:
--   Eval W: GW mul sgn P
-- statement:
--   The weight times the sign of P is the product over the layers of ws_i^(members of P in layer i),
--   or 0 if some layer has too few or too many members.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean#L173-L186
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean#L173-L186

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_MarkProf
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_PaddedDescent_F_MarkPi
import Definitions.Def_ClauseBound_TopN_EvalW
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.EvalW
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark

theorem ClauseBound.TopN.EvalW.GW_mul_sgnP (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml) {P : Finset ℕ} (hP : P ⊆ range (cls Ls).length) :
    GW Ls.length ws lo hi (fun i => (layP Ls P i).card) * sgnP Ls P =
      ∏ i ∈ range Ls.length, if lo.getD i 0 ≤ (layP Ls P i).card ∧ (layP Ls P i).card ≤ hi.getD i 0 then ws.getD i 0 ^ (layP Ls P i).card else 0 := by sorry
