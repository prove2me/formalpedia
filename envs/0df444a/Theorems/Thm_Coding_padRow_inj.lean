-- Prove2me | Theorems.Thm_Coding_padRow_inj
-- name    : Coding.padRow_inj
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:07:22.220102+00:00
-- url     : https://prove2.me/theorems/35e548c7-f522-4479-9dcc-61ead489be5c
-- title:
--   Coding: pad Row inj
-- statement:
--   Padding is one to one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L114-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Grid.lean#L114-L120

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_GridDefs
import Definitions.Def_Coding_OccLists
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_StepMachines_Math_CodeMore
import Definitions.Def_PaddedDescent_F_Table
import Definitions.Def_Eight_SecLevel_GridWords
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Grid
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Coding
open Finset Groundwork Groundwork.Prog Groundwork.Grid ClauseBound.Alg ClauseBound.Alg.GridNet Eight.SecNetworks Eight.ViaGrouping Eight.Level
variable {g : ℕ} {tr : Bool} {lam : ℕ}

theorem Coding.padRow_inj (a : Fin (nParts g g tr)) {z z' : List Bool} (hz : z.length = g * ((g * g - 1) * lam)) (hz' : z'.length = g * ((g * g - 1) * lam))
    (h : padRow g tr lam a.val z = padRow g tr lam a.val z') : z = z' := by sorry
