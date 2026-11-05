-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Dummy_cutoff_dummy
-- name    : ClauseBound.ParityChecks.Dummy.cutoff_dummy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:04:52.300486+00:00
-- url     : https://prove2.me/theorems/566b5b9f-dc2c-44ee-b878-0a9b841f854a
-- title:
--   Dummy: cutoff dummy
-- statement:
--   The cut-off lemma with dummy variables: modulo 2^{M+1} only the sets of at most M violated
--   incidences count.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean#L110-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Dummy.lean#L110-L122

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

theorem ClauseBound.ParityChecks.Dummy.cutoff_dummy (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (h : Disjoint J₁ J₂) (f : X → ℤ) (M : ℕ) :
    2 ^ r * (∑ ξ, f ξ * (∏ j ∈ J₁, ev #(Λ j ∩ V ξ)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(Λ j ∩ V ξ)) ≡
      ∑ ξ, f ξ * ∑ y : Fin r → Bool, ∑ S ∈ (inc V r Λ J₁ J₂ ξ y).powerset with #S ≤ M, (-2 : ℤ) ^ #S [ZMOD 2 ^ (M + 1)] := by sorry
