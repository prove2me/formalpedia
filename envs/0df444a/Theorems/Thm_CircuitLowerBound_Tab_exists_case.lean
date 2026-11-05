-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_exists_case
-- name    : CircuitLowerBound.Tab.exists_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:40:38.339271+00:00
-- url     : https://prove2.me/theorems/f173ae1f-3a1c-4560-a617-3aca910eca1c
-- title:
--   Tab: exists case
-- statement:
--   At every time before the last some case holds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L44-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Sound.lean#L44-L60

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

theorem CircuitLowerBound.Tab.exists_case (h : Spec N α b Q P) {t : ℕ} (ht : t < 2 ^ b) : ∃ γ, α (.cs γ) t 0 = true := by sorry
