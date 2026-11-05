-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridPresents_gridW_eq_W
-- name    : ClauseBound.Alg.GridPresents.gridW_eq_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:50:28.050477+00:00
-- url     : https://prove2.me/theorems/a502e7b3-8ce5-46d2-94e5-0cbe1e5c0245
-- title:
--   Grid Presents: grid W eq W
-- statement:
--   What `gridW` computes from a table is the weight of the network of the instance of the table.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L150-L158
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridPresents.lean#L150-L158

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_GridNet
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_ClauseBound_Alg_GridPresents
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridPresents
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg.GridNet
variable (P : PiecesF) (pad : U) (p d : ℕ) (tr : Bool) (h ℓ y : ℕ)

theorem ClauseBound.Alg.GridPresents.gridW_eq_W (T : Tab) (a : Fin (nParts p d tr)) {z : List Bool} (hz : z.length = nMemb p d tr * (p * d) * ℓ) :
    gridW p d tr ℓ T (a.val, z) = (gridN P pad p d tr h ℓ y (instOf (K := p * d) T)).W a z := by sorry
