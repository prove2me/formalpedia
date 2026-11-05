-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_gridN_c_le
-- name    : ClauseBound.Alg.GridNet.gridN_c_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:09:10.86851+00:00
-- url     : https://prove2.me/theorems/39581764-c9bd-4ed3-90f3-9c74fe749682
-- title:
--   Grid Net: grid N c le
-- statement:
--   Two parts share at most members²·mℓ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L391-L394
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L391-L394

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

theorem ClauseBound.Alg.GridNet.gridN_c_le (hP : CutsOK P pad h ℓ A) (p d : ℕ) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (p * d)) (List Bool))
    (a b : Fin (nParts p d tr)) : (gridN P pad p d tr h ℓ y Rm).c a b ≤ nMemb p d tr ^ 2 * (P.m * ℓ) := by sorry
