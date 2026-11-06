-- Prove2me | Theorems.Thm_FixedWidthSteps_absorb
-- name    : FixedWidthSteps.absorb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:25:57.642275+00:00
-- url     : https://prove2.me/theorems/11614ec1-4385-43f8-ab74-fc99960f71b0
-- title:
--   Fixed Width Steps: absorb
-- statement:
--   If t ≤ 2^{D·E(n)} and X + 1 ≤ (n + 2)^D, then q·(t + X + 1)^q ≤ 2^{C·E(n)} with C = q·(2D + 2)·c₁,
--   where E(n) = n·log log n/(log n)^α.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Absorb.lean#L69-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/FixedWidthSteps/Absorb.lean#L69-L110

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FixedWidthSteps_Small
import Definitions.Def_VariableBound_Printed_ThmVariablesA
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_FixedWidthSteps_Absorb
import Theorems.Thm_VariableBound_Paper_absorb

set_option autoImplicit false
section
section
open FixedWidthSteps
open MainTheoremForms FixedWidth

theorem FixedWidthSteps.absorb (α : ℝ) {c₁ : ℕ} (hc : 1 ≤ c₁) (hB : ∀ n : ℕ, 4 ≤ n → lg n ≤ c₁ * expVariables α n) (q D : ℕ) {n t X : ℕ} (hn : 4 ≤ n)
    (ht : (t : ℝ) ≤ (2 : ℝ) ^ ((D : ℝ) * expVariables α n)) (hX : X + 1 ≤ (n + 2) ^ D) : q * (t + X + 1) ^ q ≤ timeVariables α (q * (2 * D + 2) * c₁) n := by sorry
