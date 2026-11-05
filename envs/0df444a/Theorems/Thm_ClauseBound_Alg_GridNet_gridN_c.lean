-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_gridN_c
-- name    : ClauseBound.Alg.GridNet.gridN_c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:09:12.233405+00:00
-- url     : https://prove2.me/theorems/2b96f4d7-9ee3-4f38-bf3a-9608a8bf6076
-- title:
--   Grid Net: grid N c
-- statement:
--   The capacity of two parts is the length of their labels.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L162-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L162-L170

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

theorem ClauseBound.Alg.GridNet.gridN_c (Rm : Inst (Fin (p * d)) (List Bool)) {a b : Fin (nParts p d tr)} (hab : a ≠ b) :
    (gridN P pad p d tr h ℓ y Rm).c a b = capG P p d tr h ℓ y a b := by sorry
