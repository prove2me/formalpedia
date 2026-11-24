-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs_parts
-- name    : Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_parts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:40.399037+00:00
-- url     : https://prove2.me/theorems/7cedc895-08a4-4378-b1af-05eb912cf0aa
-- title:
--   Subset Sum Invariance: orbs parts
-- statement:
--   The Subset Sum Invariance construction uses the orbs parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean#L65-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean#L65-L89

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

theorem Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_parts (σ : Perm α) : (orbs σ).val.map Finset.card = σ.partition.parts := by sorry
