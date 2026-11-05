-- Prove2me | Theorems.Thm_ClauseBound_Alg_GridNet_stC_full
-- name    : ClauseBound.Alg.GridNet.stC_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:12:02.96928+00:00
-- url     : https://prove2.me/theorems/91c1cc49-dd35-4210-accc-6d3c75f9f086
-- title:
--   Grid Net: st C full
-- statement:
--   The Grid Net construction uses the st C full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L78-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/GridNet.lean#L78-L79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_ClauseBound_Grid_Size
import Definitions.Def_ClauseBound_Grid_Expand
import Definitions.Def_StepMachines_Math_SideNet
import Definitions.Def_ClauseBound_Alg_GridNet
import Theorems.Thm_Groundwork_Grid_stC_full

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.GridNet
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F

theorem ClauseBound.Alg.GridNet.stC_full (p d : ℕ) (tr : Bool) (n : ℕ) : (stC p d tr n).Full := by sorry
