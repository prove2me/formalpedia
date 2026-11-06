-- Prove2me | Theorems.Thm_FixedWidthSteps_timeVariables_le
-- name    : FixedWidthSteps.timeVariables_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:16:00.304233+00:00
-- url     : https://prove2.me/theorems/c97dfddb-f098-4864-b2f2-cfda77ebe7f1
-- title:
--   Fixed Width Steps: time Variables le
-- statement:
--   The bound is at most the power that it rounds down.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Small.lean#L41-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Small.lean#L41-L41

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

theorem FixedWidthSteps.timeVariables_le (α : ℝ) (C n : ℕ) : (timeVariables α C n : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * expVariables α n) := by sorry
