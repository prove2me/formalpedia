-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_inner_bound
-- name    : Formalism.FourierDecayAlt.P.S3dx4.inner_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:07:10.289629+00:00
-- url     : https://prove2.me/theorems/a350852c-29f3-5a8f-a384-77dfa1b75cc8
-- title:
--   S3dx4: inner bound
-- statement:
--   The S3dx4 construction uses the inner bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InnerBound.lean#L38-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InnerBound.lean#L38-L108

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GNMulRpow
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerBound
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

theorem Formalism.FourierDecayAlt.P.S3dx4.inner_bound (hNI : NormInv) {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : B.IsHaarOn (B.GV k r) μG)
    (hGc : ∀ᵐ x ∂μG, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) {C1 C2 a b : ℝ}
    (hb1 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e1 y‖ ≤ C1 * B.gN y ^ (-a))
    (hb2 : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e2 y‖ ≤ C2 * B.gN y ^ (-a))
    (hb0 : 0 ≤ b) (hba : b ≤ a)
    {P Q γi : Mx k r} (hP : P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hQ : Q ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hγ : γi ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ∫⁻ x, ‖e1 (P * Matrix.of x)‖ₑ * ‖e2 (Q * (γi * Matrix.of x))‖ₑ ∂μG ≤
      ENNReal.ofReal (|C1| * |C2|) * ‖B.gN (Q * γi * P⁻¹) ^ (-b)‖ₑ *
        ∫⁻ x, ‖B.gN (Matrix.of x) ^ (-(a - b))‖ₑ ∂μG := by sorry
