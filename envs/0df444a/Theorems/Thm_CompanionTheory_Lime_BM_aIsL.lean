-- Prove2me | Theorems.Thm_CompanionTheory_Lime_BM_aIsL
-- name    : CompanionTheory.Lime.BM.aIsL
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:49:40.252797+00:00
-- url     : https://prove2.me/theorems/a5794650-a719-54b7-a261-28e589ec5ced
-- title:
--   BM: a Is L
-- statement:
--   The BM construction uses the a Is L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/AtFormAdmOneOfSteps.lean#L80-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/BesselModels/AtFormAdmOneOfSteps.lean#L80-L105

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_BesselModels_AtFormAdmOneOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open CompanionTheory CompanionTheory.Lime CompanionTheory.Lime.BM
open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.QuantumDeterminants

theorem CompanionTheory.Lime.BM.aIsL (hJ : UniqGap) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ} {Wp : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    {h : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hok : GapOK k r h) (hlam : IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hc : ∀ a, c a ≠ 0) (hπ : PI.UpqRep.IsHCTypeW k r z u π) {B l : H → Wp}
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (PI.BesselMapUniq.psiGen k r z c) σ π B)
    (hl : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (PI.BesselMapUniq.psiGen k r z c) σ π l)
    (hnz : ∃ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, l x ≠ 0) :
    ∃ c0 : ℂ, ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B v = c0 • l v := by sorry
