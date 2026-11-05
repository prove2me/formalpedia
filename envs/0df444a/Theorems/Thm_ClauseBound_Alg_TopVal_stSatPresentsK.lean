-- Prove2me | Theorems.Thm_ClauseBound_Alg_TopVal_stSatPresentsK
-- name    : ClauseBound.Alg.TopVal.stSatPresentsK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:44:50.719846+00:00
-- url     : https://prove2.me/theorems/93a2dd2f-5370-4ffc-b210-7aebc7ad6dea
-- title:
--   Top Val: st Sat Presents K
-- statement:
--   The plain functions satFk, in the context ((g, k) in unary, ψ), present the network of ψ on g
--   nodes at width k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopVal.lean#L37-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/TopVal.lean#L37-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Top
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_CountKSat_Value
import Definitions.Def_CountKSat_InOut
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_ClauseBound_Alg_TopVal
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.TopVal
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count PaddedDescent PaddedDescent.F CountKSat

theorem ClauseBound.Alg.TopVal.stSatPresentsK : StSatPresentsK := by sorry
