-- Prove2me | Theorems.Thm_AppRunningTime_groupingSizes
-- name    : AppRunningTime.groupingSizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:56:35.962538+00:00
-- url     : https://prove2.me/theorems/92c3e0a9-0ac4-45a7-8c53-d64378875b0a
-- title:
--   App Running Time: grouping Sizes
-- statement:
--   The lemma on groupings with explicit cost, end of the proof: K ≤ g in both cases, and L ≤ gP + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Main.lean#L88-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Main.lean#L88-L89

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Series_Deriv
import Definitions.Def_GeneralPieces_GenF_Main
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Series_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_GeneralPieces_Ring_Dual
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_GeneralPieces_Ring_Pieces
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Definitions.Def_GeneralPieces_DefGenPieces_MayAssume
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_GeneralPieces_Group_Calls
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Half_Main
import Definitions.Def_GeneralPieces_Tied_Bound
import Definitions.Def_GeneralPieces_Main
import Theorems.Thm_GeneralPieces_groupingSizes

set_option autoImplicit false
section
section
open AppRunningTime

theorem AppRunningTime.groupingSizes : GroupingSizes := by sorry
