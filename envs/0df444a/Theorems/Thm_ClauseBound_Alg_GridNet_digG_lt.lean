-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_digG_lt
-- name    : ClauseBound.Alg.GridNet.digG_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:41:57.707848+00:00
-- url     : https://prove2.me/theorems/78e324af-f85c-4737-a181-fdeb0fa6e0ea
-- title:
--   Grid Net: dig G lt
-- statement:
--   A digit of a pattern is the number of a piece.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L348-L351
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L348-L351

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

theorem ClauseBound.Alg.GridNet.digG_lt (hP : 1 ≤ P.cnt h ℓ) (d : ℕ) (tr : Bool) (y q κ : ℕ) : digG P d tr h ℓ y q κ < P.cnt h ℓ := by sorry
