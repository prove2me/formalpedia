-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_gridN_sized
-- name    : ClauseBound.Alg.GridNet.gridN_sized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:25:28.639338+00:00
-- url     : https://prove2.me/theorems/44f951d7-afa4-42de-9e07-64e48b9b408b
-- title:
--   Grid Net: grid N sized
-- statement:
--   The network on words has the size m·(parts·members²·ℓ), and values of at most members·B +
--   members²·bits bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L369-L380
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L369-L380

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
variable {P : PiecesF} {pad : U} {h ℓ : ℕ} {A : ℕ → Pieces.Four ℓ}

theorem ClauseBound.Alg.GridNet.gridN_sized (hP : CutsOK P pad h ℓ A) (p d : ℕ) (tr : Bool) (y : ℕ) {B : ℕ} {Rm : Inst (Fin (p * d)) (List Bool)}
    (hR : BoundedInst ℓ B Rm) :
    (gridN P pad p d tr h ℓ y Rm).Sized (P.m * (nParts p d tr * nMemb p d tr ^ 2 * ℓ))
      (nMemb p d tr * B + nMemb p d tr ^ 2 * P.bits h ℓ) := by sorry
