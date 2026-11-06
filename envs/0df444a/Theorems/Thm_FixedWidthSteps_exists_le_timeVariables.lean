-- Prove2me | Theorems.Thm_FixedWidthSteps_exists_le_timeVariables
-- name    : FixedWidthSteps.exists_le_timeVariables
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:18:18.839482+00:00
-- url     : https://prove2.me/theorems/98ca2e59-85a1-4d82-a005-4e515d6182ac
-- title:
--   Fixed Width Steps: exists le time Variables
-- statement:
--   For one n ≥ 4, every number is within the bound for some C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Small.lean#L44-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Small.lean#L44-L51

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

theorem FixedWidthSteps.exists_le_timeVariables (α : ℝ) {n : ℕ} (hn : 4 ≤ n) (N : ℕ) : ∃ C : ℕ, N ≤ timeVariables α C n := by sorry
