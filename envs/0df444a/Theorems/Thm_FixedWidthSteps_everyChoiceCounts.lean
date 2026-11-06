-- Prove2me | Theorems.Thm_FixedWidthSteps_everyChoiceCounts
-- name    : FixedWidthSteps.everyChoiceCounts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:54:48.71566+00:00
-- url     : https://prove2.me/theorems/c613545f-8cb6-4c67-9566-721926af4073
-- title:
--   Fixed Width Steps: every Choice Counts
-- statement:
--   The step of Theorem A (c), second sentence, that rests on the «In particular» of Theorem D (a):
--   its conditions hold for all but finitely many n, the other n are within the bound, and k ≤ 2 is read
--   as 3.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Main.lean#L42-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Main.lean#L42-L43

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
set_option autoImplicit false
section
section
open FixedWidthSteps

theorem FixedWidthSteps.everyChoiceCounts : EveryChoiceCounts := by sorry
