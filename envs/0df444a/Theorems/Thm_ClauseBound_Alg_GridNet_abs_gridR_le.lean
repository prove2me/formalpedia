-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_abs_gridR_le
-- name    : ClauseBound.Alg.GridNet.abs_gridR_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:12:50.112961+00:00
-- url     : https://prove2.me/theorems/fd595a6e-d0f4-40ac-8907-4032a6535f54
-- title:
--   Grid Net: abs grid R le
-- statement:
--   The bound 2^B on the instance at the queries that are asked passes to the grid.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L320-L329
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L320-L329

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

theorem ClauseBound.Alg.GridNet.abs_gridR_le {p d n B : ℕ} (tr : Bool) {Rm : Inst (Fin (p * d)) (List Bool)} (hR : BoundedInst n B Rm)
    (w : Fin (nParts p d tr) × Fin (nMemb p d tr)) (h : Fin (nParts p d tr) × Fin (nMemb p d tr) → Bits n) :
    |gridR p d tr n Rm w h| ≤ 2 ^ B := by sorry
