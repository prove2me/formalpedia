-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_value_gridN
-- name    : ClauseBound.Alg.GridNet.value_gridN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:13:48.094224+00:00
-- url     : https://prove2.me/theorems/bca11322-c0bf-4681-8951-716f9e00b020
-- title:
--   Grid Net: value grid N
-- statement:
--   Either network on words has the value of the term.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L354-L358
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L354-L358

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

theorem ClauseBound.Alg.GridNet.value_gridN (hP : CutsOK P pad h ℓ A) (p d : ℕ) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) :
    (gridN P pad p d tr h ℓ y Rm).value = termZ p d ℓ Rm A (P.cnt h ℓ - 1) y := by sorry
