-- Prove2me | Theorems.Thm_FixedWidth_runningTimesFromPieces
-- name    : FixedWidth.runningTimesFromPieces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:09:07.766432+00:00
-- url     : https://prove2.me/theorems/48024b07-0c0c-4b94-a5f4-90e9130c6d99
-- title:
--   Fixed Width: running Times From Pieces
-- statement:
--   Theorem A, with both sentences of (c) with the printed hypotheses and quantifiers, in steps of a
--   Turing machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Main.lean#L58-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Main.lean#L58-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_Numbers
import Definitions.Def_FixedWidthSteps_Small
import Definitions.Def_FixedWidthSteps_Hypothesis
import Definitions.Def_FixedWidthSteps_Choice
import Definitions.Def_FixedWidthSteps_Sentence
import Definitions.Def_PairsToBound_Pairs
import Definitions.Def_PairsToBound_Width
import Definitions.Def_PairsToBound_FrontEnd
import Definitions.Def_PairsToBound_Exhaust
import Definitions.Def_TwoMachines_Main
import Definitions.Def_RecursionToBound_Main
import Definitions.Def_OccurM_Main
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_FixedWidthSteps_Main
import Theorems.Thm_ClausesOccur_runningTimesFromPieces

set_option autoImplicit false
section
section
open FixedWidth
open FixedWidthSteps

theorem FixedWidth.runningTimesFromPieces : RunningTimesFromPieces := by sorry
