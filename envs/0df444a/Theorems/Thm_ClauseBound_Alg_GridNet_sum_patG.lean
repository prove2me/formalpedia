-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_sum_patG
-- name    : ClauseBound.Alg.GridNet.sum_patG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:13:49.952281+00:00
-- url     : https://prove2.me/theorems/3a78b0c2-3956-4334-87b0-f57362710a1c
-- title:
--   Grid Net: sum pat G
-- statement:
--   Summing over the numbers y < (n+1)^R is summing over the patterns.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L222-L261
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L222-L261

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

theorem ClauseBound.Alg.GridNet.sum_patG (p d n : ℕ) (F : (Rect (Fin p) (Fin d) → ℕ) → ℤ) :
    ∑ y ∈ range ((n + 1) ^ nRectG p d), F (patG p d n y) =
      ∑ ι ∈ tuples (fun ω => ω ∈ Ω (Fin p) (Fin d)) (fun _ => range (n + 1)) 0, F ι := by sorry
