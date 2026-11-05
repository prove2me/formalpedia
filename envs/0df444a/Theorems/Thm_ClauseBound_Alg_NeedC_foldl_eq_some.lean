-- Prove2me | Theorems.Thm_ClauseBound_Alg_NeedC_foldl_eq_some
-- name    : ClauseBound.Alg.NeedC.foldl_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:13.38097+00:00
-- url     : https://prove2.me/theorems/2efd4ea6-2628-442e-b98e-7aed1b63197b
-- title:
--   Need C: foldl eq some
-- statement:
--   If the bound b is at least the largest exponent at the start and `needG`, no cut-off at 100·(b + 2)
--   is active.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean#L100-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean#L100-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_NeedC
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.NeedC
open Groundwork PaddedDescent.F

theorem ClauseBound.Alg.NeedC.foldl_eq_some (P : PiecesF) {pad : U} {b : ℕ} (hp : 100 * (b + 2) ≤ pad.length) (sched : List Step) (st : NState)
    (h : tot P st sched ≤ b) :
    sched.foldl (fun o s => cap pad none (o.map fun st => needStep P st s)) (some st) = some (sched.foldl (needStep P) st) := by sorry
