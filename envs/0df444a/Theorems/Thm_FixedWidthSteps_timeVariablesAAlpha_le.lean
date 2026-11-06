-- Prove2me | Theorems.Thm_FixedWidthSteps_timeVariablesAAlpha_le
-- name    : FixedWidthSteps.timeVariablesAAlpha_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:31:55.613639+00:00
-- url     : https://prove2.me/theorems/693545fb-a88b-48d3-bc00-3099aa69bd3f
-- title:
--   Fixed Width Steps: time Variables AAlpha le
-- statement:
--   The time of the «In particular» of Theorem D (a) at the width w is at most 2^{C·w²·E(n)}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Choice.lean#L29-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Choice.lean#L29-L34

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

theorem FixedWidthSteps.timeVariablesAAlpha_le (C w n : ℕ) (α : ℝ) : (timeVariablesAAlpha C w n α : ℝ) ≤ (2 : ℝ) ^ (((C * w ^ 2 : ℕ) : ℝ) * expVariables α n) := by sorry
