-- Prove2me | Theorems.Thm_ClauseBound_Alg_NeedC_tot_cons
-- name    : ClauseBound.Alg.NeedC.tot_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:34:35.185906+00:00
-- url     : https://prove2.me/theorems/3f4db8a1-b23b-4eae-a486-a6b53f385900
-- title:
--   Need C: tot cons
-- statement:
--   A step does not change `tot`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean#L38-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/NeedC.lean#L38-L39

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

theorem ClauseBound.Alg.NeedC.tot_cons (P : PiecesF) (st : NState) (s : Step) (r : List Step) : tot P (needStep P st s) r = tot P st (s :: r) := by sorry
