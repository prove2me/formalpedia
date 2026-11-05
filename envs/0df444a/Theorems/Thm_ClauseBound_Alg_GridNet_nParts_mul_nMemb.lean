-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_nParts_mul_nMemb
-- name    : ClauseBound.Alg.GridNet.nParts_mul_nMemb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:47:37.776497+00:00
-- url     : https://prove2.me/theorems/98ea627e-02ba-4064-9b82-a4f6a398e412
-- title:
--   Grid Net: n Parts mul n Memb
-- statement:
--   There are p·d nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L51-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L51-L54

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

theorem ClauseBound.Alg.GridNet.nParts_mul_nMemb (p d : ℕ) (tr : Bool) : nParts p d tr * nMemb p d tr = p * d := by sorry
