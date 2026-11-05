-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_StepOne_cutoff_one
-- name    : ClauseBound.ParityChecks.StepOne.cutoff_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:38.192273+00:00
-- url     : https://prove2.me/theorems/8213ec70-d1ee-4bf8-b3d9-19dcc4171a2f
-- title:
--   Step One: cutoff one
-- statement:
--   The cut-off lemma for one ξ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L177-L189
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/StepOne.lean#L177-L189

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
variable {E : Type} {r : ℕ}

theorem ClauseBound.ParityChecks.StepOne.cutoff_one {J₁ J₂ : Finset (Fin r)} (hJ : Disjoint J₁ J₂) (A : Fin r → Finset E) {ν M : ℕ} (hν : 1 ≤ ν) (hM : ν - 1 + #J₁ ≤ M) :
    (∏ j ∈ J₁, ev #(A j)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(A j) ≡
      ∑ S ∈ (Fintype.piFinset (dom A (J₁ ∪ J₂))).filter (fun S => ∑ j, #(S j) ≤ M), (∏ j ∈ J₁, sig #(S j)) * ∏ j ∈ J₂, (-2 : ℤ) ^ #(S j)
      [ZMOD 2 ^ ν] := by sorry
