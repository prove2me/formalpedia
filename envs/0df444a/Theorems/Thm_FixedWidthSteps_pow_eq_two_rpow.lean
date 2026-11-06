-- Prove2me | Theorems.Thm_FixedWidthSteps_pow_eq_two_rpow
-- name    : FixedWidthSteps.pow_eq_two_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:25:17.479632+00:00
-- url     : https://prove2.me/theorems/cac277cc-884d-4708-86c2-d21e837c3c97
-- title:
--   Fixed Width Steps: pow eq two rpow
-- statement:
--   x^m = 2^{m·log x}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Absorb.lean#L28-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Absorb.lean#L28-L29

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

theorem FixedWidthSteps.pow_eq_two_rpow {x : ℝ} (hx : 0 < x) (m : ℕ) : x ^ m = (2 : ℝ) ^ ((m : ℝ) * lg x) := by sorry
