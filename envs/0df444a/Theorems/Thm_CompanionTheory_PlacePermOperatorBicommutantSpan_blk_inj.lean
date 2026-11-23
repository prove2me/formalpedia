-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_blk_inj
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.blk_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:57:10.384801+00:00
-- url     : https://prove2.me/theorems/8d9cb5cc-6a60-44cb-ae67-143dde3e20a6
-- title:
--   Place Perm Operator Bicommutant Span: blk inj
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the blk inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L26-L32

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.blk_inj {a b c d a' b' c' d' : K} {r s u w r' s' u' w' : Fin M → K} {U U' : Matrix (Fin M) (Fin M) K}
    (h : blk a b r c d s u w U = blk a' b' r' c' d' s' u' w' U') :
    a = a' ∧ b = b' ∧ r = r' ∧ c = c' ∧ d = d' ∧ s = s' ∧ u = u' ∧ w = w' ∧ U = U' := by sorry
