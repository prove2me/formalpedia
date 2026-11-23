-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_CISum_isIrr_of_isIrreducible
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum.isIrr_of_isIrreducible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:10:50.823867+00:00
-- url     : https://prove2.me/theorems/c30126f0-aac6-422d-9113-839ef84cd8ba
-- title:
--   CISum: is Irr of is Irreducible
-- statement:
--   The CISum construction uses the is Irr of is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CentralIdempotentsSumOne.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CentralIdempotentsSumOne.lean#L59-L70

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CentralIdempotentsSumOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum.isIrr_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : IsIrr ρ := by sorry
