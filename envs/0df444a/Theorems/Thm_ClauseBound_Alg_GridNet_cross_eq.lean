-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_cross_eq
-- name    : ClauseBound.Alg.GridNet.cross_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:12:18.753459+00:00
-- url     : https://prove2.me/theorems/db380726-a4ad-464d-820b-e1c9a811c95e
-- title:
--   Grid Net: cross eq
-- statement:
--   The function [x = v][y = u], `Pieces.cross`, agrees with `Cross.X`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L288-L290
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L288-L290

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

theorem ClauseBound.Alg.GridNet.cross_eq {n : ℕ} (x y u v : Bits n) : Pieces.cross x y u v = Cross.X x y u v := by sorry
