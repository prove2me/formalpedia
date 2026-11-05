-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_acc_of_spec
-- name    : CircuitLowerBound.Tab.acc_of_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:40:58.095886+00:00
-- url     : https://prove2.me/theorems/73ccb939-129f-412b-86a5-1010456703af
-- title:
--   Tab: acc of spec
-- statement:
--   If the conditions can be satisfied, the machine accepts.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L193-L213
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L193-L213

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Sound
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
variable {N} [Finite (Case N)] {α : Atom N → ℕ → ℕ → Bool} {b Q P : ℕ}

theorem CircuitLowerBound.Tab.acc_of_spec (hP : P + 2 ≤ 2 ^ b) (h : Spec N α b (b + lamOf N) P) : Acc N P (2 ^ b) := by sorry
