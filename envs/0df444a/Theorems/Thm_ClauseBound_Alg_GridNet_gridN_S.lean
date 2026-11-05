-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_gridN_S
-- name    : ClauseBound.Alg.GridNet.gridN_S
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:48:00.420958+00:00
-- url     : https://prove2.me/theorems/f9ce99a8-f97c-4d17-b2d7-59db279fc82a
-- title:
--   Grid Net: grid N S
-- statement:
--   The Grid Net construction uses the grid N S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L158-L159
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L158-L159

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)
variable {P pad p d tr h ℓ y}
variable (P pad p d tr h ℓ y)

theorem ClauseBound.Alg.GridNet.gridN_S (Rm : Inst (Fin (p * d)) (List Bool)) (a : Fin (nParts p d tr)) :
    (gridN P pad p d tr h ℓ y Rm).S a = words (nMemb p d tr * (p * d) * ℓ) := by sorry
