-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_gridCl_D
-- name    : ClauseBound.Alg.GridPresents.gridCl_D
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:50:46.364212+00:00
-- url     : https://prove2.me/theorems/17dad640-b0cd-48c4-bb91-9c2df55035e1
-- title:
--   Grid Presents: grid Cl D
-- statement:
--   The Grid Presents construction uses the grid Cl D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L164-L168
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L164-L168

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)
variable {P pad p d tr h ℓ y}

theorem ClauseBound.Alg.GridPresents.gridCl_D (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b) :
    (gridCl P pad p d tr h ℓ y R a b).D = ((vC (nMemb p d tr) ℓ).prod (rectsC P pad p d tr h ℓ y a b)).D := by sorry
