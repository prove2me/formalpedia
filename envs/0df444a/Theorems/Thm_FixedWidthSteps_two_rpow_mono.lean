-- Prove2me | Theorems.Thm_FixedWidthSteps_two_rpow_mono
-- name    : FixedWidthSteps.two_rpow_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:22:17.853899+00:00
-- url     : https://prove2.me/theorems/84571ddd-fb2f-4f7f-8acc-86976f44dc81
-- title:
--   Fixed Width Steps: two rpow mono
-- statement:
--   2^{a·E} ≤ 2^{b·E} for a ≤ b and E ≥ 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Absorb.lean#L32-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Absorb.lean#L32-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_Small
import Definitions.Def_VariableBound_Printed_ThmVariablesA
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_FixedWidthSteps_Absorb
set_option autoImplicit false
section
section
open FixedWidthSteps
open MainTheoremForms FixedWidth

theorem FixedWidthSteps.two_rpow_mono {a b : ℕ} (h : a ≤ b) {E : ℝ} (hE : 0 ≤ E) : (2 : ℝ) ^ ((a : ℝ) * E) ≤ (2 : ℝ) ^ ((b : ℝ) * E) := by sorry
