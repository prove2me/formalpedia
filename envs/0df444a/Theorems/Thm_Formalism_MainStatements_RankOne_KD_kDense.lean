-- Prove2me | Theorems.Thm_Formalism_MainStatements_RankOne_KD_kDense
-- name    : Formalism.MainStatements.RankOne.KD.kDense
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:55:09.916841+00:00
-- url     : https://prove2.me/theorems/84acf094-0a2b-44bf-8c5e-b6278146c6b0
-- title:
--   KD: k Dense
-- statement:
--   The KD construction uses the k Dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/RankOneTori/KDense.lean#L201-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/RankOneTori/KDense.lean#L201-L254

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
open PI.UpqRep

theorem Formalism.MainStatements.RankOne.KD.kDense (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat (2 * r + k + 1) → (H →L[ℂ] H)) (hlam : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) (v : H)
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) (Ws : List (List (Mat (2 * r + k + 1))))
    (hWs : ∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) (e : ℝ) (he : 0 < e) :
    ∃ v' : H, IsKFinHpk (k := k) (r := r) σ v' ∧ (Ws.map fun w => ‖dsigW (k := k) (r := r) σ w (v - v')‖).sum < e := by sorry
