-- Prove2me | Theorems.Thm_FixedWidthSteps_lg_facts
-- name    : FixedWidthSteps.lg_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:17:05.821196+00:00
-- url     : https://prove2.me/theorems/fa01620e-1ba0-4ea1-b0d0-f14cba9e91a4
-- title:
--   Fixed Width Steps: lg facts
-- statement:
--   For n ≥ 4: log n ≥ 2 and log log n ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Small.lean#L23-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Small.lean#L23-L27

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

theorem FixedWidthSteps.lg_facts {n : ℕ} (hn : 4 ≤ n) : 2 ≤ lg n ∧ 1 ≤ lg (lg n) := by sorry
