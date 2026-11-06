-- Prove2me | Theorems.Thm_FixedWidthSteps_expVariables_pos
-- name    : FixedWidthSteps.expVariables_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:17:36.382781+00:00
-- url     : https://prove2.me/theorems/9232dd2b-c6e3-481d-af1b-22ba95857723
-- title:
--   Fixed Width Steps: exp Variables pos
-- statement:
--   For n ≥ 4 the exponent is positive.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Small.lean#L30-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Small.lean#L30-L34

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

theorem FixedWidthSteps.expVariables_pos (α : ℝ) {n : ℕ} (hn : 4 ≤ n) : 0 < expVariables α n := by sorry
