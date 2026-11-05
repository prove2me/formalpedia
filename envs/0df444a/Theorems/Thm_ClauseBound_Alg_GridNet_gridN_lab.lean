-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_gridN_lab
-- name    : ClauseBound.Alg.GridNet.gridN_lab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:25:13.450349+00:00
-- url     : https://prove2.me/theorems/ffe4f84f-3e2d-4061-90b7-4871ca9ed173
-- title:
--   Grid Net: grid N lab
-- statement:
--   The labels of two parts are all words of that length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L173-L179
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L173-L179

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

theorem ClauseBound.Alg.GridNet.gridN_lab (Rm : Inst (Fin (p * d)) (List Bool)) {a b : Fin (nParts p d tr)} (hab : a ≠ b) :
    (gridN P pad p d tr h ℓ y Rm).lab a b = words (capG P p d tr h ℓ y a b) := by sorry
