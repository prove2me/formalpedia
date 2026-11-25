-- Prove2me | Theorems.Thm_Formalism_MainStatements_RankOne_KD_fin_of_finAlg
-- name    : Formalism.MainStatements.RankOne.KD.fin_of_finAlg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:19:15.483917+00:00
-- url     : https://prove2.me/theorems/74da9ade-c50b-5cd5-984f-f91aebe9b458
-- title:
--   KD: fin of fin Alg
-- statement:
--   The KD construction uses the fin of fin Alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/RankOneTori/KDense.lean#L166-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/RankOneTori/KDense.lean#L166-L196

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfIwasawa
import Definitions.Def_CompanionTheory_AutomorphicTheory_RankOneTori_KDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open Formalism Formalism.MainStatements Formalism.MainStatements.RankOne Formalism.MainStatements.RankOne.KD
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm
variable {n : ℕ} {K : Set (Mat n)} {hK : IsMatGroup K}
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] {G : Set (Mat n)}
  {σ : Mat n → (H →L[ℂ] H)} [CompactSpace (MG K hK)]

theorem Formalism.MainStatements.RankOne.KD.fin_of_finAlg (hG : IsMatGroup G) (hKG : K ⊆ G) (h : RepOn G σ) {v : H} (hv : IsSm G σ v)
    {p : C(MG K hK, ℝ)} (hp : p ∈ finAlg (MG K hK)) :
    ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ (∫ g, p g • σ g.mat v ∂haar) ∈ S ∧ ∀ a ∈ K, ∀ x ∈ S, σ a x ∈ S := by sorry
