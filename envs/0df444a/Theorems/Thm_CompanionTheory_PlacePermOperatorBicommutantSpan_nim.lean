-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_nim
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.nim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:46.787297+00:00
-- url     : https://prove2.me/theorems/93ffad91-bd4e-4d46-b030-4e317f24c7f4
-- title:
--   Place Perm Operator Bicommutant Span: nim
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the nim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L148-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/ParAlg.lean#L148-L150

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

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.nim (w : Fin M → K) (z a d : K) (U : Matrix (Fin M) (Fin M) K) :
    nM s J w z * pm 1 0 0 1 0 U * pm a 0 0 d 0 1 = pm a (z * d) (-(((s ∘ w) ᵥ* J) ᵥ* U)) d (d • w) U := by sorry
