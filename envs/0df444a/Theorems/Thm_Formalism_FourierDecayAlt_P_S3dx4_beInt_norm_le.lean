-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_beInt_norm_le
-- name    : Formalism.FourierDecayAlt.P.S3dx4.beInt_norm_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:22:36.419972+00:00
-- url     : https://prove2.me/theorems/5cf1aa20-e852-4bfa-bc4c-dcd31b08939c
-- title:
--   S3dx4: be Int norm le
-- statement:
--   The S3dx4 construction uses the be Int norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L1QuotientIntegralBound.lean#L37-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L1QuotientIntegralBound.lean#L37-L58

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMemMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L1QuotientIntegralBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.S3dx4.beInt_norm_le {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {x v : H} {g : Mx k r} (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r}
    (hp : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r) :
    ‖beInt z c π σ (σ g x) v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * g) x⟫_ℂ‖ := by sorry
