-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_gridE_symm_val
-- name    : ClauseBound.Alg.GridNet.gridE_symm_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:47:30.696008+00:00
-- url     : https://prove2.me/theorems/8fa681b4-c019-4473-a904-b7f7b39fc38d
-- title:
--   Grid Net: grid E symm val
-- statement:
--   The position of a node of the grid among the p·d nodes of the instance.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L41-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L41-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_Groundwork_Grid_gridE_symm_val

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F

theorem ClauseBound.Alg.GridNet.gridE_symm_val (p d : ℕ) (tr : Bool) (w : Fin (nParts p d tr) × Fin (nMemb p d tr)) :
    ((gridE p d tr).symm w : ℕ) = nodeG d tr w.1 w.2 := by sorry
