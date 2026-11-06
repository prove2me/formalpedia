-- Prove2me | Theorems.Thm_FixedWidthSteps_timeVariables_mono
-- name    : FixedWidthSteps.timeVariables_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:17:22.487196+00:00
-- url     : https://prove2.me/theorems/97aab8d4-c3ad-4c2f-a0dd-e22f0375dc05
-- title:
--   Fixed Width Steps: time Variables mono
-- statement:
--   The bound grows with C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Small.lean#L37-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Small.lean#L37-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_RouteDefs
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_FixedWidthSteps_Small
set_option autoImplicit false
section
section
open FixedWidthSteps
open MainTheoremForms FixedWidth

theorem FixedWidthSteps.timeVariables_mono (α : ℝ) {C C' n : ℕ} (hn : 4 ≤ n) (h : C ≤ C') : timeVariables α C n ≤ timeVariables α C' n := by sorry
