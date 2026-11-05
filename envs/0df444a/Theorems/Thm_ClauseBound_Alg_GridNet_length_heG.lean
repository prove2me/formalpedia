-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_length_heG
-- name    : ClauseBound.Alg.GridNet.length_heG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:34:12.168206+00:00
-- url     : https://prove2.me/theorems/7eb0cb53-2d71-4edd-ae63-f2367027e9be
-- title:
--   Grid Net: length he G
-- statement:
--   A half-edge in the word of a state has ℓ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L57-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L57-L62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F

theorem ClauseBound.Alg.GridNet.length_heG {p d ℓ : ℕ} {tr : Bool} {z : List Bool} (hz : z.length = nMemb p d tr * (p * d) * ℓ) {x u : ℕ}
    (hx : x < nMemb p d tr) (hu : u < p * d) : (heG p d ℓ z x u).length = ℓ := by sorry
