-- Prove2me | Theorems.Thm_ClauseBound_Alg_NeedC_needFin_foldl
-- name    : ClauseBound.Alg.NeedC.needFin_foldl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:25:19.362035+00:00
-- url     : https://prove2.me/theorems/e7e8a919-7431-4925-9a2d-104c4c5e53b2
-- title:
--   Need C: need Fin foldl
-- statement:
--   Without cut-offs the computation gives the larger of the largest exponent at the start and
--   `needG`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean#L43-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean#L43-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Alg_NeedC
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.NeedC
open Groundwork PaddedDescent.F

theorem ClauseBound.Alg.NeedC.needFin_foldl (P : PiecesF) (sched : List Step) (st : NState) : needFin (sched.foldl (needStep P) st) = tot P st sched := by sorry
