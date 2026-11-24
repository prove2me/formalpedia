-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_CISum_centralIdem_act
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum.centralIdem_act
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:15.372702+00:00
-- url     : https://prove2.me/theorems/09bc2662-93ef-4e22-b8fc-2590a60364c2
-- title:
--   CISum: central Idem act
-- statement:
--   The CISum construction uses the central Idem act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CentralIdempotentsSumOne.lean#L11-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CentralIdempotentsSumOne.lean#L11-L57

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
open Classical

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum.centralIdem_act {G V W : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (hρ : IsIrr ρ) (hσ : IsIrr σ) :
    σ.asAlgebraHom (centralIdem ρ) = if Nonempty (Representation.Equiv ρ σ) then 1 else 0 := by sorry
