-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_gridN_W
-- name    : ClauseBound.Alg.GridPresents.gridN_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:26:23.557233+00:00
-- url     : https://prove2.me/theorems/e4f2c04c-6f42-43ab-a8c1-d88c5d7bfa5e
-- title:
--   Grid Presents: grid N W
-- statement:
--   The weight of the part a at the word z of a state.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L128-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L128-L147

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
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)

theorem ClauseBound.Alg.GridPresents.gridN_W (Rm : Inst (Fin (p * d)) (List Bool)) (a : Fin (nParts p d tr)) {z : List Bool}
    (hz : z.length = nMemb p d tr * (p * d) * ℓ) :
    (gridN P pad p d tr h ℓ y Rm).W a z =
      (∏ i : Fin (nMemb p d tr), if (heG p d ℓ z i (nodeG d tr a i)).all (!·) = true then
          Rm ((gridE p d tr).symm (a, i)) (fun u => if u = (gridE p d tr).symm (a, i) then [] else heG p d ℓ z i u)
        else 0) *
      ∏ q ∈ pairs (Fin (nMemb p d tr)), if heG p d ℓ z q.1 (nodeG d tr a q.2) = heG p d ℓ z q.2 (nodeG d tr a q.1) then 1 else 0 := by sorry
