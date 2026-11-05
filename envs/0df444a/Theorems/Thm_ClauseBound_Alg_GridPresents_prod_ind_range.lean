-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_prod_ind_range
-- name    : ClauseBound.Alg.GridPresents.prod_ind_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:26:13.411256+00:00
-- url     : https://prove2.me/theorems/290a6327-7866-468c-a840-304453637088
-- title:
--   Grid Presents: prod ind range
-- statement:
--   A product of indicators is the indicator of the test on all i < n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L32-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L32-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet

theorem ClauseBound.Alg.GridPresents.prod_ind_range (n : ℕ) (t : ℕ → Bool) :
    ∏ i : Fin n, (if t i = true then (1 : ℤ) else 0) = if (List.range n).all t = true then 1 else 0 := by sorry
