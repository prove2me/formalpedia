-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_evals_of_stay
-- name    : CircuitLowerBound.Tab.evals_of_stay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:40:38.059561+00:00
-- url     : https://prove2.me/theorems/2c7de2ce-82f1-4daa-8862-20d6e1c1ab25
-- title:
--   Tab: evals of stay
-- statement:
--   What the step that stays reaches in T steps, Mathlib's step function reaches in at most T steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L235-L254
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L235-L254

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)

theorem CircuitLowerBound.Tab.evals_of_stay {h : N.tm.Cfg} : ∀ (T : ℕ) (c₀ : N.tm.Cfg), (stay N)^[T] c₀ = h →
    ∃ n ≤ T, (flip bind N.tm.step)^[n] (some c₀) = some h := by sorry
