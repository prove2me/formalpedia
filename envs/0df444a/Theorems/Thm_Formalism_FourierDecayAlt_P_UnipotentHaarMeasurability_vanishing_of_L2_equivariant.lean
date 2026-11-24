-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_vanishing_of_L2_equivariant
-- name    : Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.vanishing_of_L2_equivariant
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:12:47.977455+00:00
-- url     : https://prove2.me/theorems/c1fbef4c-e4ac-4de9-be74-b9394ad2d670
-- title:
--   Unipotent Haar Measurability: vanishing of L2 equivariant
-- statement:
--   The Unipotent Haar Measurability construction uses the vanishing of L2 equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VanishingOfL2Equivariant.lean#L18-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VanishingOfL2Equivariant.lean#L18-L42

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZeroOfAe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VanishingOfL2Equivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 3200000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability
open Formalism.FourierDecayAlt.ThreeDimData

theorem Formalism.FourierDecayAlt.P.UnipotentHaarMeasurability.vanishing_of_L2_equivariant {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)}
    {w0 : H} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hBC : BeConv) (hIn : Inputs)
    (hS : Side k r ε lam h σ w0 z c u π μW μN μG νq)
    {x : H} (hx : x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) {v : H} (hv : IsAdm σ w0 v)
    (hl : ∀ ξ : Wp, PI.BesselPeriodGGP.l2SG νq (fun g => be z c π σ μW μN (σ g x) v ξ) = 0) :
    be z c π σ μW μN x v = 0 := by sorry
