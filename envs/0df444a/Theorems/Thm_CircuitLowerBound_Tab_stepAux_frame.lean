-- Prove2me | Theorems.Thm_CircuitLowerBound_Tab_stepAux_frame
-- name    : CircuitLowerBound.Tab.stepAux_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:40:20.62818+00:00
-- url     : https://prove2.me/theorems/9c045f44-31ab-4c54-be92-9c63961b63c9
-- title:
--   Tab: step Aux frame
-- statement:
--   What lies below the top d symbols is neither seen nor changed.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L37-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Frame.lean#L37-L90

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

theorem CircuitLowerBound.Tab.stepAux_frame (q : TM2.Stmt Γ Λ σ) : ∀ (v : σ) (A R : ∀ k, List (Γ k)), (∀ k, ops q ≤ (A k).length ∨ R k = []) →
    TM2.stepAux q v (fun k => A k ++ R k) =
      ⟨(TM2.stepAux q v A).l, (TM2.stepAux q v A).var, fun k => (TM2.stepAux q v A).stk k ++ R k⟩ := by sorry
