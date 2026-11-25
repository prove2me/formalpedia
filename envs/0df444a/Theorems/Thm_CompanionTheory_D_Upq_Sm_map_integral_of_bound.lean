-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Sm_map_integral_of_bound
-- name    : CompanionTheory.D.Upq.Sm.map_integral_of_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:04:48.239497+00:00
-- url     : https://prove2.me/theorems/a35c74d7-2051-59ae-83a5-b59ba4d6263e
-- title:
--   Sm: map integral of bound
-- statement:
--   The Sm construction uses the map integral of bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ParametricIntegralSmoothness/IntCommute.lean#L94-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/ParametricIntegralSmoothness/IntCommute.lean#L94-L147

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_Exists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ParametricIntegralSmoothness_IntCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff Manifold Convolution
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)} {hG : IsMatGroup G}
variable {μ : Measure (MG G hG)} [IsFiniteMeasureOnCompacts μ] {φ : MG G hG → ℂ}

theorem CompanionTheory.D.Upq.Sm.map_integral_of_bound (h : RepOn G σ) {v : H} (hv : IsSm G σ v) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hy : IsSm G σ (∫ g, φ g • σ g.mat v ∂μ)) {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {B : H → V}
    (hadd : ∀ x, IsSm G σ x → ∀ y, IsSm G σ y → B (x + y) = B x + B y)
    (hsmul : ∀ (a : ℂ) x, IsSm G σ x → B (a • x) = a • B x) {ι : Type} [Fintype ι]
    {W : ι → List (Mat n)} (hW : ∀ i, LieW G (W i)) {C : ℝ}
    (hB : ∀ x, IsSm G σ x → ‖B x‖ ≤ C * ∑ i, ‖dsW σ (W i) x‖) :
    B (∫ g, φ g • σ g.mat v ∂μ) = ∫ g, φ g • B (σ g.mat v) ∂μ := by sorry
