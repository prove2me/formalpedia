-- Prove2me | Theorems.Thm_ClauseBound_Alg_NeedC_eq_of_foldl_eq_some
-- name    : ClauseBound.Alg.NeedC.eq_of_foldl_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:31.15578+00:00
-- url     : https://prove2.me/theorems/bafdbeb4-57e0-4f71-81b4-12c17c57bbd1
-- title:
--   Need C: eq of foldl eq some
-- statement:
--   A result of the computation with cut-offs is the result of the computation without.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean#L85-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean#L85-L96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_NeedC
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.NeedC
open Groundwork PaddedDescent.F

theorem ClauseBound.Alg.NeedC.eq_of_foldl_eq_some (P : PiecesF) (pad : U) (sched : List Step) (st st' : NState)
    (h : sched.foldl (fun o s => cap pad none (o.map fun st => needStep P st s)) (some st) = some st') :
    st' = sched.foldl (needStep P) st := by sorry
