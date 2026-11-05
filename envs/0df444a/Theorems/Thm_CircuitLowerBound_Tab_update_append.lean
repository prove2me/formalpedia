-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_update_append
-- name    : CircuitLowerBound.Tab.update_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:40:28.484458+00:00
-- url     : https://prove2.me/theorems/58e514a6-cc21-4724-b9c6-9b100c1ad6a6
-- title:
--   Tab: update append
-- statement:
--   The Tab construction uses the update append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L29-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L29-L34

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
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

theorem CircuitLowerBound.Tab.update_append (A R : ∀ k, List (Γ k)) (k : K) (w : List (Γ k)) :
    Function.update (fun k => A k ++ R k) k (w ++ R k) = fun k' => Function.update A k w k' ++ R k' := by sorry
