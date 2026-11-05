-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_presents
-- name    : ClauseBound.Alg.GridPresents.presents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:26:14.703234+00:00
-- url     : https://prove2.me/theorems/28f249a9-5341-4414-ab6f-4044478e3fca
-- title:
--   Grid Presents: presents
-- statement:
--   The functions of `gridF` are the weights and the factors of `gridN` for the instance of the
--   table, on all words of the right lengths.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L278-L285
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L278-L285

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_presents
import Theorems.Thm_PaddedDescent_F_RebalF_presents
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet

theorem ClauseBound.Alg.GridPresents.presents (P : PiecesF) (pad pu du hu ℓu : U) (tr : Bool) (y : ℕ) (T : Tab) :
    (gridF P).toP.Presents ((pad, (pu, du), tr, hu), (ℓu, y, T))
      (gridN P pad pu.length du.length tr hu.length ℓu.length y (instOf (K := pu.length * du.length) T)) 0 0 := by sorry
