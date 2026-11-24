-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs_eq
-- name    : Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:34.239801+00:00
-- url     : https://prove2.me/theorems/c4b4a55f-b297-4858-a8ec-ebdb27cb169d
-- title:
--   Subset Sum Invariance: orbs eq
-- statement:
--   The Subset Sum Invariance construction uses the orbs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean#L52-L57

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

theorem Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_eq {σ : Perm α} {O O' : Finset α} (hO : O ∈ orbs σ) (hO' : O' ∈ orbs σ) {x : α}
    (h1 : x ∈ O) (h2 : x ∈ O') : O = O' := by sorry
