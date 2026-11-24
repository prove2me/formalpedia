-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_lint_left
-- name    : Formalism.FourierDecayAlt.P.S3dx4.lint_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:00:32.361863+00:00
-- url     : https://prove2.me/theorems/23b65d8f-d538-4ac9-a668-0d183c5872e1
-- title:
--   S3dx4: lint left
-- statement:
--   The S3dx4 construction uses the lint left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GNMulRpow.lean#L42-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GNMulRpow.lean#L42-L50

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MapInvMEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GNMulRpow
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

theorem Formalism.FourierDecayAlt.P.S3dx4.lint_left {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : B.IsHaarOn (B.GV k r) μG)
    {a : Mx k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) {F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F (Formalism.QuantumDeterminants.lmulM a x) ∂μG = ∫⁻ x, F x ∂μG := by sorry
