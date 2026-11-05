-- Prove2me | Theorems.Thm_ClauseBound_Alg_NeedC_foldl_none
-- name    : ClauseBound.Alg.NeedC.foldl_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:35:23.139281+00:00
-- url     : https://prove2.me/theorems/0cec0c8e-f5e7-43d8-9e1d-b11bb6f345a6
-- title:
--   Need C: foldl none
-- statement:
--   A state that was thrown away stays away.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean#L74-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean#L74-L82

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

theorem ClauseBound.Alg.NeedC.foldl_none (P : PiecesF) (pad : U) (sched : List Step) :
    sched.foldl (fun o s => cap pad none (o.map fun st => needStep P st s)) (none : Option NState) = none := by sorry
