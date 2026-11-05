-- Prove2me | Theorems.Thm_ClauseBound_Gen_End_topK_eq
-- name    : ClauseBound.Gen.End.topK_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:16:53.859066+00:00
-- url     : https://prove2.me/theorems/f2693e72-061c-4a49-8eec-d3b97c98cb03
-- title:
--   End: top K eq
-- statement:
--   The number of nodes at the top of a schedule, without a case distinction on the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/End.lean#L33-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Gen/End.lean#L33-L36

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Alg_Prog
import Definitions.Def_PaddedDescent_F_SideF
import Definitions.Def_ClauseBound_Gen_PartA
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Gen_End
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen
open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen
open ClauseBound.Gen.End

theorem ClauseBound.Gen.End.topK_eq (i : List Step × U) :
    topK i = bif i.1.isEmpty then i.2.length else (i.1.headD (([], [], []), ([], []), (false, [], []))).p * (i.1.headD (([], [], []), ([], []), (false, [], []))).d := by sorry
