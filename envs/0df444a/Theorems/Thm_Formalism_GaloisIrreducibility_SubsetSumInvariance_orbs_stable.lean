-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs_stable
-- name    : Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_stable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:11.71561+00:00
-- url     : https://prove2.me/theorems/e7686583-b2b4-453f-8746-cdd7a0b15b36
-- title:
--   Subset Sum Invariance: orbs stable
-- statement:
--   The Subset Sum Invariance construction uses the orbs stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean#L16-L25

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

theorem Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_stable {σ : Perm α} {O : Finset α} (hO : O ∈ orbs σ) : ∀ x ∈ O, σ x ∈ O := by sorry
