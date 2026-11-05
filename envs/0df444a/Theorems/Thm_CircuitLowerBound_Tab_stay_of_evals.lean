-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_stay_of_evals
-- name    : CircuitLowerBound.Tab.stay_of_evals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:28:37.498706+00:00
-- url     : https://prove2.me/theorems/3224e60a-da14-478f-8d30-c75b7824be27
-- title:
--   Tab: stay of evals
-- statement:
--   A run of n steps of Mathlib's step function is a run of the step that stays.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L217-L232
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L217-L232

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

theorem CircuitLowerBound.Tab.stay_of_evals {c₀ c : N.tm.Cfg} : ∀ n : ℕ, (flip bind N.tm.step)^[n] (some c₀) = some c → (stay N)^[n] c₀ = c := by sorry
