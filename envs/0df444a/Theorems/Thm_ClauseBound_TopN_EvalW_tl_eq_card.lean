-- Prove2me | Theorems.Thm_ClauseBound_TopN_EvalW_tl_eq_card
-- name    : ClauseBound.TopN.EvalW.tl_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:43:48.202212+00:00
-- url     : https://prove2.me/theorems/08d2f9b1-abed-4b57-9ef3-00e3043a3e73
-- title:
--   Eval W: tl eq card
-- statement:
--   If P has the profile y, the profile prescribes for layer i the number of members of P in layer
--   i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean#L56-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean#L56-L59

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

theorem ClauseBound.TopN.EvalW.tl_eq_card {k g n : ℕ} {Ls : List Fml} {y : ℕ} {P : Finset ℕ} (hg : 0 < g) (hW : WfL k n Ls) (hP : P ⊆ range (cls Ls).length)
    (hM : Match g n Ls y P) {i : ℕ} (hi : i < Ls.length) : tl g Ls y i = (layP Ls P i).card := by sorry
