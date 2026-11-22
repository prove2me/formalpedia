-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_exists_le_map
-- name    : Formalism.GaloisIrreducibility.SubsetSumInvariance.exists_le_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:25:23.071709+00:00
-- url     : https://prove2.me/theorems/4734e3a0-28d8-47cc-aa12-b8b388ad0e5c
-- title:
--   Subset Sum Invariance: exists le map
-- statement:
--   The Subset Sum Invariance construction uses the exists le map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean#L95-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PermSubSumInv.lean#L95-L115

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

theorem Formalism.GaloisIrreducibility.SubsetSumInvariance.exists_le_map {β γ : Type*} (f : β → γ) (m : Multiset β) :
    ∀ s : Multiset γ, s ≤ m.map f → ∃ t ≤ m, t.map f = s := by sorry
