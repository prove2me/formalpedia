-- Prove2me | Theorems.Thm_FixedWidthSteps_everyChoiceCountsFrom
-- name    : FixedWidthSteps.everyChoiceCountsFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:31:47.141332+00:00
-- url     : https://prove2.me/theorems/277b65cd-e73b-41d7-93e3-d32f255b8923
-- title:
--   Fixed Width Steps: every Choice Counts From
-- statement:
--   The main statement, from the «In particular» of Theorem D (a), the conditions for all but
--   finitely many n, the finitely many other n, and the facts on the width that the algorithm takes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Choice.lean#L38-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Choice.lean#L38-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_Absorb
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_FixedWidthSteps_Choice
set_option autoImplicit false
section
section
open FixedWidthSteps
open Turing Groundwork ClauseBound.Alg MainTheoremForms TwoMachines PairsToBound FixedWidth Wrap

theorem FixedWidthSteps.everyChoiceCountsFrom : EveryChoiceCountsFrom := by sorry
