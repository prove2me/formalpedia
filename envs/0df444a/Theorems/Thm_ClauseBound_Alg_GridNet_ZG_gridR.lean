-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_ZG_gridR
-- name    : ClauseBound.Alg.GridNet.ZG_gridR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:48:42.583218+00:00
-- url     : https://prove2.me/theorems/644d7a5d-ee35-4ef4-935b-c375e861c5d9
-- title:
--   Grid Net: ZG grid R
-- statement:
--   The sum over the grid, or over the transposed grid, is the term.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L309-L317
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L309-L317

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

theorem ClauseBound.Alg.GridNet.ZG_gridR (p d : ℕ) (tr : Bool) (ℓ : ℕ) (Rm : Inst (Fin (p * d)) (List Bool)) (A : ℕ → Pieces.Four ℓ) (n y : ℕ) :
    ZG (gridR p d tr ℓ Rm) (fun ω => trA tr (A (digit n y (rectIxG d tr (tri ω.1.1 ω.1.2) (tri ω.2.1 ω.2.2))))) =
      termZ p d ℓ Rm A n y := by sorry
