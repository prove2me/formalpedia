-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_abs_trA_le
-- name    : ClauseBound.Alg.GridNet.abs_trA_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:48:37.596552+00:00
-- url     : https://prove2.me/theorems/35794076-b224-4eef-8839-e16990c6b47a
-- title:
--   Grid Net: abs tr A le
-- statement:
--   The values of a piece read on the transposed grid.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L361-L365
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L361-L365

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

theorem ClauseBound.Alg.GridNet.abs_trA_le {b : ℕ} {F : Pieces.Four ℓ} (hF : ∀ x y u v, |F x y u v| ≤ 2 ^ b) (tr : Bool) (x y u v : Bits ℓ) :
    |trA tr F x y u v| ≤ 2 ^ b := by sorry
