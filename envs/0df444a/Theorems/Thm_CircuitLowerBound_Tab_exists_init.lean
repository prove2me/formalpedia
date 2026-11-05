-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_exists_init
-- name    : CircuitLowerBound.Tab.exists_init
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:40:52.654176+00:00
-- url     : https://prove2.me/theorems/7a3253e2-f474-4341-a48a-6dd71981eb2e
-- title:
--   Tab: exists init
-- statement:
--   The first row is the start of the machine on 1^P 0 y, for some y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L85-L163
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L85-L163

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

theorem CircuitLowerBound.Tab.exists_init (h : Spec N α b Q P) (hP : P + 1 < 2 ^ Q) :
    ∃ y : List Bool, Enc N α 0 (2 ^ Q) (initList N.tm ((unary P ++ y).map N.inputAlphabet.invFun)) := by sorry
