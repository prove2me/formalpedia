-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_length_stepAux_le
-- name    : CircuitLowerBound.Tab.length_stepAux_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:40:20.851237+00:00
-- url     : https://prove2.me/theorems/a2dfd06a-e391-4d9d-8f11-0a5d72c80f71
-- title:
--   Tab: length step Aux le
-- statement:
--   A statement with d stack operations makes a stack longer by at most d.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L93-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L93-L119

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

theorem CircuitLowerBound.Tab.length_stepAux_le (q : TM2.Stmt Γ Λ σ) : ∀ (v : σ) (A : ∀ k, List (Γ k)) (k : K),
    ((TM2.stepAux q v A).stk k).length ≤ (A k).length + ops q := by sorry
