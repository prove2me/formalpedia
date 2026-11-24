-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs_sub
-- name    : Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:59.258038+00:00
-- url     : https://prove2.me/theorems/9c97ffd2-36f5-4994-a8d9-63836e9f344f
-- title:
--   Subset Sum Invariance: orbs sub
-- statement:
--   The Subset Sum Invariance construction uses the orbs sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean#L37-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean#L37-L50

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
open Formalism.GaloisIrreducibility.SubsetSumInvariance
open Equiv Equiv.Perm Finset
variable {α : Type} [Fintype α] [DecidableEq α]

theorem Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_sub {σ : Perm α} {A : Finset α} (hA : ∀ x ∈ A, σ x ∈ A) {O : Finset α}
    (hO : O ∈ orbs σ) {x : α} (hxO : x ∈ O) (hxA : x ∈ A) : O ⊆ A := by sorry
