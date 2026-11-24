-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs_pd
-- name    : Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_pd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:41.359806+00:00
-- url     : https://prove2.me/theorems/5a6cd996-7d6c-48c5-a9e7-4f6cd3bbe7db
-- title:
--   Subset Sum Invariance: orbs pd
-- statement:
--   The Subset Sum Invariance construction uses the orbs pd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean#L59-L63

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

theorem Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_pd (σ : Perm α) : (orbs σ : Set (Finset α)).PairwiseDisjoint id := by sorry
