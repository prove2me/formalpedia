-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_lambda_left_translation
-- name    : Formalism.FourierDecayAlt.P.S3dx4.lambda_left_translation
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:41:56.750991+00:00
-- url     : https://prove2.me/theorems/6975e233-9937-4445-af86-088b92163490
-- title:
--   S3dx4: lambda left translation
-- statement:
--   The S3dx4 construction uses the lambda left translation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableEnormComposition.lean#L143-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableEnormComposition.lean#L143-L166

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousSandwichedProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableEnormComposition
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

theorem Formalism.FourierDecayAlt.P.S3dx4.lambda_left_translation {e0 : Mx k r → ℂ} (he0 : Continuous e0) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z)
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    Lam1 e0 (μW.prod μN) (fun i j => (h0 * n0 * Matrix.of x) i j) y = Lam1 e0 (μW.prod μN) x y := by sorry
