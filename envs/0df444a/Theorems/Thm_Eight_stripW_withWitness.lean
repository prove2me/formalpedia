-- Prove2me | Theorems.Thm_Eight_stripW_withWitness
-- name    : Eight.stripW_withWitness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:33:48.259474+00:00
-- url     : https://prove2.me/theorems/89317a62-e904-486c-80ab-b4cbcd8afa49
-- title:
--   Eight: strip W with Witness
-- statement:
--   `stripW` takes the witness off.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/NSETH.lean#L63-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/NSETH.lean#L63-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_NSETHDefs
import Definitions.Def_Eight_Cor_Defs
import Definitions.Def_Eight_Level_End
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_KSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_WidthK_Top_EndLemmas
import Definitions.Def_WidthK_Decode
import Definitions.Def_SparsifyWidthK_DefsProg
import Definitions.Def_GraphProblems_Host
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_NSETH
set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog Paper Turing

theorem Eight.stripW_withWitness (w x : List Bool) : stripW (withWitness w x) = x := by sorry
