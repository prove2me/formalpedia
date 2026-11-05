-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_ixG_bijOn
-- name    : ClauseBound.Alg.GridNet.ixG_bijOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:13:33.169275+00:00
-- url     : https://prove2.me/theorems/412966a9-bd39-48b4-9c1a-9d7ae7e491fd
-- title:
--   Grid Net: ix G bij On
-- statement:
--   The rectangles are numbered 0, …, R − 1, each number once.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L189-L209
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L189-L209

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

theorem ClauseBound.Alg.GridNet.ixG_bijOn (p d : ℕ) : Set.BijOn (ixG p d) (Ω (Fin p) (Fin d)) (range (nRectG p d)) := by sorry
