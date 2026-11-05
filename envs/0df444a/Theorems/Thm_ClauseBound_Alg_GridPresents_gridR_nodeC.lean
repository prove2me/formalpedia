-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_gridR_nodeC
-- name    : ClauseBound.Alg.GridPresents.gridR_nodeC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:49:38.492803+00:00
-- url     : https://prove2.me/theorems/f031064e-e2e8-4512-8e3b-feb544cd8dd3
-- title:
--   Grid Presents: grid R node C
-- statement:
--   The tensor of a node of the grid, at the word of the half-edges that start at this node: 0
--   unless the block at the node's own position is all zeros.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L110-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L110-L122

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet

theorem ClauseBound.Alg.GridPresents.gridR_nodeC (p d : ℕ) (tr : Bool) (n : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) (w : Fin (nParts p d tr) × Fin (nMemb p d tr))
    {wn : List Bool} (h : wn.length = p * d * n) :
    gridR p d tr n Rm w ((nodeC p d tr n).dec wn) =
      if (block n ((gridE p d tr).symm w) wn).all (!·) = true then
        Rm ((gridE p d tr).symm w) (fun u => if u = (gridE p d tr).symm w then [] else block n u wn)
      else 0 := by sorry
