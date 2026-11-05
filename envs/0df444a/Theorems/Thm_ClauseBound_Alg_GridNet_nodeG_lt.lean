-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_nodeG_lt
-- name    : ClauseBound.Alg.GridNet.nodeG_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:26:59.59371+00:00
-- url     : https://prove2.me/theorems/2003c416-c363-4ed8-a099-6dd58d479d95
-- title:
--   Grid Net: node G lt
-- statement:
--   Positions are below p·d.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L46-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L46-L48

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

theorem ClauseBound.Alg.GridNet.nodeG_lt {p d : ℕ} (tr : Bool) {a i : ℕ} (ha : a < nParts p d tr) (hi : i < nMemb p d tr) : nodeG d tr a i < p * d := by sorry
