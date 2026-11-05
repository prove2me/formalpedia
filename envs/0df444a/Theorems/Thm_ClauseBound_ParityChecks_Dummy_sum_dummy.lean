-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Dummy_sum_dummy
-- name    : ClauseBound.ParityChecks.Dummy.sum_dummy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:14.788436+00:00
-- url     : https://prove2.me/theorems/cb04f03d-1b24-4cd2-a225-cdd73ac9d9aa
-- title:
--   Dummy: sum dummy
-- statement:
--   2^r·∏_{j ∈ J₁} [|V_j(ξ)| even]·∏_{j ∈ J₂} (−1)^{|V_j(ξ)|} is the sum over the dummy variables y
--   and over all sets S of violated incidences of (−2)^|S|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean#L93-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean#L93-L99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_ClauseBound_ParityChecks_Dummy
set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Dummy
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype X]

theorem ClauseBound.ParityChecks.Dummy.sum_dummy (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (h : Disjoint J₁ J₂) (ξ : X) :
    ∑ y : Fin r → Bool, ∑ S ∈ (inc V r Λ J₁ J₂ ξ y).powerset, (-2 : ℤ) ^ #S =
      2 ^ r * ((∏ j ∈ J₁, ev #(Λ j ∩ V ξ)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(Λ j ∩ V ξ)) := by sorry
