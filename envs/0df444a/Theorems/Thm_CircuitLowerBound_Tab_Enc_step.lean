-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_Enc_step
-- name    : CircuitLowerBound.Tab.Enc.step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:01:30.132787+00:00
-- url     : https://prove2.me/theorems/0fc8ec97-f24c-4ee5-9752-2830ad1e77e0
-- title:
--   Enc: step
-- statement:
--   From a row to the next.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L63-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L63-L82

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

theorem CircuitLowerBound.Tab.Enc.step (h : Spec N α b Q P) {t V : ℕ} {c : N.tm.Cfg} (ht : t < 2 ^ b) (hE : Enc N α t V c) (hd : dep N ≤ V) (hV : V ≤ 2 ^ Q) :
    Enc N α (t + 1) (V - dep N) (stay N c) := by sorry
