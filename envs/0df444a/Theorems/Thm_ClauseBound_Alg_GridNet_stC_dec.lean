-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_stC_dec
-- name    : ClauseBound.Alg.GridNet.stC_dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:41:22.82236+00:00
-- url     : https://prove2.me/theorems/b0e9497c-b679-4df6-b7a9-376810cbf69d
-- title:
--   Grid Net: st C dec
-- statement:
--   The state named by a word, read half-edge by half-edge.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L82-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L82-L85

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_Groundwork_Grid_stC_dec

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F

theorem ClauseBound.Alg.GridNet.stC_dec (p d : ℕ) (tr : Bool) (n : ℕ) (z : List Bool) (x : Fin (nMemb p d tr)) (w' : Fin (nParts p d tr) × Fin (nMemb p d tr)) :
    (stC p d tr n).dec z x w' = Grid.bitsOf n (heG p d n z x (nodeG d tr w'.1 w'.2)) := by sorry
