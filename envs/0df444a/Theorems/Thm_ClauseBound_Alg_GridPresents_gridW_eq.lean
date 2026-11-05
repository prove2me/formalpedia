-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_gridW_eq
-- name    : ClauseBound.Alg.GridPresents.gridW_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:50:01.05173+00:00
-- url     : https://prove2.me/theorems/de41c2e2-a3b7-4773-8cd9-9767c29b9cd9
-- title:
--   Grid Presents: grid W eq
-- statement:
--   The weight of the part a at the word z: the product of the entries of its nodes (0 unless the
--   half-edge of a node to itself is all zeros), times the tests that the two ends
--   of every edge inside the part agree.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L58-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L58-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet

theorem ClauseBound.Alg.GridPresents.gridW_eq (p d : ℕ) (tr : Bool) (ℓ : ℕ) (T : Tab) (a : ℕ) (z : List Bool) :
    gridW p d tr ℓ T (a, z) =
      (∏ i : Fin (nMemb p d tr), if (heG p d ℓ z i (nodeG d tr a i)).all (!·) = true then
          look T (nodeG d tr a i, (List.range (p * d)).map fun u => if u = nodeG d tr a i then [] else heG p d ℓ z i u)
        else 0) *
      ∏ q ∈ pairs (Fin (nMemb p d tr)), if heG p d ℓ z q.1 (nodeG d tr a q.2) = heG p d ℓ z q.2 (nodeG d tr a q.1) then 1 else 0 := by sorry
