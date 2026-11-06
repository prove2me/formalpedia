-- Prove2me | Theorems.Thm_FixedWidthSteps_lg_le_exp
-- name    : FixedWidthSteps.lg_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:22:31.106697+00:00
-- url     : https://prove2.me/theorems/ad6352b6-2905-465c-9d25-d76e9788dbf0
-- title:
--   Fixed Width Steps: lg le exp
-- statement:
--   log n ≤ c₁·n·log log n/(log n)^α for all n ≥ 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Absorb.lean#L36-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Absorb.lean#L36-L65

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

theorem FixedWidthSteps.lg_le_exp (hSmall : SmallCasesAreWithinTheBound) (α : ℝ) (hα : 0 ≤ α) : ∃ c₁ : ℕ, 1 ≤ c₁ ∧ ∀ n : ℕ, 4 ≤ n → lg n ≤ c₁ * expVariables α n := by sorry
