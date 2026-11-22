-- Prove2me | Theorems.Thm_Formalism_SLP_P_CountO_ncard_biUnion_le
-- name    : Formalism.SLP.P.CountO.ncard_biUnion_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:04:28.312982+00:00
-- url     : https://prove2.me/theorems/1199149b-506d-4e50-8c06-356d580db6f1
-- title:
--   Count O: ncard bi Union le
-- statement:
--   The Count O construction uses the ncard bi Union le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/CountO.lean#L420-L431
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/CountO.lean#L420-L431

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
open NumberField
variable (E : Type) [Field E] [NumberField E]
variable {E}

theorem Formalism.SLP.P.CountO.ncard_biUnion_le {α β : Type} (s : Finset β) (t : β → Set α)
    (ht : ∀ b ∈ s, (t b).Finite) :
    (⋃ b ∈ s, t b).Finite ∧ (⋃ b ∈ s, t b).ncard ≤ ∑ b ∈ s, (t b).ncard := by sorry
