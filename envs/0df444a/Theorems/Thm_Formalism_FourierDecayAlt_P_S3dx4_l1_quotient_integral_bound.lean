-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_l1_quotient_integral_bound
-- name    : Formalism.FourierDecayAlt.P.S3dx4.l1_quotient_integral_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:21:26.32102+00:00
-- url     : https://prove2.me/theorems/48b68aa1-7b59-4fec-b23d-3d2ed3a51afa
-- title:
--   S3dx4: l1 quotient integral bound
-- statement:
--   The S3dx4 construction uses the l1 quotient integral bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L1QuotientIntegralBound.lean#L78-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/L1QuotientIntegralBound.lean#L78-L141

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

theorem Formalism.FourierDecayAlt.P.S3dx4.l1_quotient_integral_bound {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (hGm : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq)
    {x v : H} {C a : ℝ}
    (hC : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖⟪v, σ y x⟫_ℂ‖ ≤ C * B.gN y ^ (-a))
    (hI : Integrable (fun y : Formalism.QuantumDeterminants.Mt k r => B.gN (Matrix.of y) ^ (-a)) μG) :
    ∫⁻ g, (∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) ∂νq < ⊤ := by sorry
