-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_exists_invariant_of_isSubSum
-- name    : Formalism.GaloisIrreducibility.exists_invariant_of_isSubSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:04.585612+00:00
-- url     : https://prove2.me/theorems/99d7b0f5-e85b-45ba-a900-e46efc3a6a86
-- title:
--   Galois Irreducibility: exists invariant of is Sub Sum
-- statement:
--   The Galois Irreducibility construction uses the exists invariant of is Sub Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean#L120-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean#L120-L134

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open SubsetSumInvariance

theorem Formalism.GaloisIrreducibility.exists_invariant_of_isSubSum {α : Type} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (a : ℕ)
    (h : IsSubSum σ.partition.parts a) : ∃ A : Finset α, (∀ x ∈ A, σ x ∈ A) ∧ A.card = a := by sorry
