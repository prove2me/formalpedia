-- Prove2me | Theorems.Thm_Eight_stripW_polyT
-- name    : Eight.stripW_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:34:17.293124+00:00
-- url     : https://prove2.me/theorems/3ebfb7ea-c831-41f4-96b5-aa472bcb56cb
-- title:
--   Eight: strip W poly T
-- statement:
--   `stripW` is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/NSETH.lean#L75-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/NSETH.lean#L75-L75

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

theorem Eight.stripW_polyT : PolyT stripW := by sorry
