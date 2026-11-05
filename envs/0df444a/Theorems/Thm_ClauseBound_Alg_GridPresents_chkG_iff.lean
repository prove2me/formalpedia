-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_chkG_iff
-- name    : ClauseBound.Alg.GridPresents.chkG_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:26:41.154507+00:00
-- url     : https://prove2.me/theorems/352f94b5-7d81-42f9-80d6-86a7afc8f65e
-- title:
--   Grid Presents: chk G iff
-- statement:
--   The test of `gridW`, spelled out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L46-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L46-L53

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

theorem ClauseBound.Alg.GridPresents.chkG_iff (p d : ℕ) (tr : Bool) (ℓ a : ℕ) (z : List Bool) :
    chkG p d tr ℓ (a, z) = true ↔
      (∀ i : Fin (nMemb p d tr), (heG p d ℓ z i (nodeG d tr a i)).all (!·) = true) ∧
      ∀ q ∈ pairs (Fin (nMemb p d tr)), heG p d ℓ z q.1 (nodeG d tr a q.2) = heG p d ℓ z q.2 (nodeG d tr a q.1) := by sorry
