-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_block_matrix_transpose
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.block_matrix_transpose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:13.327251+00:00
-- url     : https://prove2.me/theorems/589844bc-119d-4f51-9544-5e04dd97b21b
-- title:
--   Place Perm Operator Bicommutant Span: block matrix transpose
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the block matrix transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L66-L70

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_ParAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.block_matrix_transpose (a b c d : K) (r s u w : Fin M → K) (U : Matrix (Fin M) (Fin M) K) :
    (blk a b r c d s u w U)ᵀ = blk a c u b d w r s Uᵀ := by sorry
