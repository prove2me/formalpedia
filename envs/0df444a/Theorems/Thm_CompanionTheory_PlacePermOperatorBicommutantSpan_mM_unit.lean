-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_mM_unit
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.mM_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:52.975889+00:00
-- url     : https://prove2.me/theorems/7a72ea2d-29bf-4207-ace3-dede9517181f
-- title:
--   Place Perm Operator Bicommutant Span: m M unit
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the m M unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L116-L120

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
variable (s : K →+* K) (J : Matrix (Fin M) (Fin M) K)
variable {s J}

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.mM_unit (hs : ∀ x, s (s x) = x) (a : Kˣ) :
    cT s (pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1) * hypJ J * pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1 = hypJ J := by sorry
