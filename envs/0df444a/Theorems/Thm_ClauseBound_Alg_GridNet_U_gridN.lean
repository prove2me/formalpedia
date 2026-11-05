-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_U_gridN
-- name    : ClauseBound.Alg.GridNet.U_gridN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:25:22.048817+00:00
-- url     : https://prove2.me/theorems/d2119ec8-1809-4e51-bf3b-d3ebb63bfdf3
-- title:
--   Grid Net: U grid N
-- statement:
--   The total of the network.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L383-L388
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L383-L388

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

theorem ClauseBound.Alg.GridNet.U_gridN (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) :
    (gridN P pad p d tr h ℓ y Rm).U = totalG P p d tr h ℓ y := by sorry
