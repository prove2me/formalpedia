-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_mem_gridCl_D
-- name    : ClauseBound.Alg.GridPresents.mem_gridCl_D
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:51:10.271205+00:00
-- url     : https://prove2.me/theorems/726dbadb-7db8-481f-8a39-4fb283690cfc
-- title:
--   Grid Presents: mem grid Cl D
-- statement:
--   Every word of the right length names a label of the parts a < b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L177-L186
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L177-L186

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)
variable {P pad p d tr h ℓ y}

theorem ClauseBound.Alg.GridPresents.mem_gridCl_D (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b)
    {θ : List Bool} (hθ : θ.length = nMemb p d tr * ℓ + ∑ κ ∈ range (c2 (nMemb p d tr)), lenG P d tr h ℓ y (tri a b) κ) :
    θ ∈ (gridCl P pad p d tr h ℓ y R a b).D := by sorry
