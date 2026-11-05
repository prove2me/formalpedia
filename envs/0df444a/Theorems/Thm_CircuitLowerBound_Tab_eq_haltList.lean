-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_eq_haltList
-- name    : CircuitLowerBound.Tab.eq_haltList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:40:50.687568+00:00
-- url     : https://prove2.me/theorems/11cdcb6d-2f60-48d8-9d5b-786b43228926
-- title:
--   Tab: eq halt List
-- statement:
--   The last row is the halted configuration with the output 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L166-L190
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L166-L190

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

theorem CircuitLowerBound.Tab.eq_haltList (h : Spec N α b Q P) {V : ℕ} {c : N.tm.Cfg} (hE : Enc N α (2 ^ b) V c) (hV : 2 ≤ V) :
    c = haltList N.tm [N.outputAlphabet.invFun true] := by sorry
