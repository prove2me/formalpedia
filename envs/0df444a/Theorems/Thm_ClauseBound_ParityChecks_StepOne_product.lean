-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_StepOne_product
-- name    : ClauseBound.ParityChecks.StepOne.product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:26.811911+00:00
-- url     : https://prove2.me/theorems/e6c5119c-3894-4c63-bfe1-d8591173f96f
-- title:
--   Step One: product
-- statement:
--   The Step One construction uses the product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L88-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L88-L98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks

theorem ClauseBound.ParityChecks.StepOne.product {X E : Type} [DecidableEq E] (V : X → Finset E) (nb r : ℕ) (Λ : ℕ → Finset E) (hG : ∀ ξ, nb < #(V ξ) → ∃ j < r, Odd #(Λ j ∩ V ξ))
    (ξ : X) : (∑ S ∈ (V ξ).powerset with #S ≤ nb, (-1 : ℤ) ^ #S) * ∏ j ∈ range r, ev #(Λ j ∩ V ξ) = if V ξ = ∅ then 1 else 0 := by sorry
