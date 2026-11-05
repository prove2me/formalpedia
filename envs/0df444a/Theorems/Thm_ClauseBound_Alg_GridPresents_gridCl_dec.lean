-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_gridCl_dec
-- name    : ClauseBound.Alg.GridPresents.gridCl_dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:50:47.276458+00:00
-- url     : https://prove2.me/theorems/865a2357-8bf9-4f1c-89df-c9f1bd4e52b6
-- title:
--   Grid Presents: grid Cl dec
-- statement:
--   The Grid Presents construction uses the grid Cl dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L170-L174
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L170-L174

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

theorem ClauseBound.Alg.GridPresents.gridCl_dec (R : Inst (Fin (nParts p d tr) × Fin (nMemb p d tr)) (Bits ℓ)) {a b : Fin (nParts p d tr)} (hab : a < b) :
    (gridCl P pad p d tr h ℓ y R a b).dec = ((vC (nMemb p d tr) ℓ).prod (rectsC P pad p d tr h ℓ y a b)).dec := by sorry
