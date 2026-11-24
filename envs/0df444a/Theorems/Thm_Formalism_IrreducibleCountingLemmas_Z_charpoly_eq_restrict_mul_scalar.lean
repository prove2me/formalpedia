-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_charpoly_eq_restrict_mul_scalar
-- name    : Formalism.IrreducibleCountingLemmas.Z.charpoly_eq_restrict_mul_scalar
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:44.075718+00:00
-- url     : https://prove2.me/theorems/e56cb118-ea14-4200-8a17-c487e89527a7
-- title:
--   Z: charpoly eq restrict mul scalar
-- statement:
--   The Z construction uses the charpoly eq restrict mul scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CardLtAddCardGtAddCardEq.lean#L592-L604
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CardLtAddCardGtAddCardEq.lean#L592-L604

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z

theorem Formalism.IrreducibleCountingLemmas.Z.charpoly_eq_restrict_mul_scalar {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A B : Submodule K V) (γ₀ : Module.End K V) (c : K) (hAB : IsCompl A B)
    (hA0 : ∀ v ∈ A, γ₀ v ∈ A) (hB0 : ∀ v ∈ B, γ₀ v = c • v) :
    γ₀.charpoly = (γ₀.restrict hA0).charpoly * (X - C c) ^ Module.finrank K B := by sorry
