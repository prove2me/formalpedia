-- Prove2me | Theorems.Thm_ClauseBound_TopN_EvalW_sum_powerset_Icc
-- name    : ClauseBound.TopN.EvalW.sum_powerset_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:43:57.996825+00:00
-- url     : https://prove2.me/theorems/9ee4e389-10ad-4942-9203-f22bc3f45bd0
-- title:
--   Eval W: sum powerset Icc
-- statement:
--   The sum of s^|P| over the subsets P of S with lo ≤ |P| ≤ hi is Σ_{lo ≤ j ≤ hi} s^j·C(|S|, j).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean#L145-L163
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean#L145-L163

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

theorem ClauseBound.TopN.EvalW.sum_powerset_Icc {ι : Type*} (S : Finset ι) (lo hi : ℕ) (s : ℤ) :
    ∑ P ∈ S.powerset, (if lo ≤ P.card ∧ P.card ≤ hi then s ^ P.card else 0) = ∑ j ∈ Icc lo hi, s ^ j * (S.card.choose j : ℤ) := by sorry
