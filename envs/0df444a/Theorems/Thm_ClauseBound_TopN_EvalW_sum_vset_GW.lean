-- Prove2me | Theorems.Thm_ClauseBound_TopN_EvalW_sum_vset_GW
-- name    : ClauseBound.TopN.EvalW.sum_vset_GW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:44:29.482127+00:00
-- url     : https://prove2.me/theorems/440e129b-d1d4-4c2a-91dd-403853729c2b
-- title:
--   Eval W: sum vset GW
-- statement:
--   For one assignment: the sum over the sets of violated clauses, with the weight `GW`, is the
--   product over the layers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean#L190-L215
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/EvalW.lean#L190-L215

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
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.EvalW
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark

theorem ClauseBound.TopN.EvalW.sum_vset_GW (σ : ℕ → Bool) (w : ℕ) (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml) (hw : ∀ i < Ls.length, hi.getD i 0 ≤ w) :
    (∑ P ∈ (vset σ Ls).powerset,
      if ∀ i < Ls.length, (layP Ls P i).card ≤ w then GW Ls.length ws lo hi (fun i => (layP Ls P i).card) * sgnP Ls P else 0) =
      ((List.range Ls.length).map fun i =>
        ∑ j ∈ Finset.Icc (lo.getD i 0) (hi.getD i 0), ws.getD i 0 ^ j * ((nvio σ (Ls.getD i [])).choose j : ℤ)).prod := by sorry
