-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_lam_right
-- name    : Formalism.FourierDecayAlt.P.S3dx4.lam_right
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:13:14.759476+00:00
-- url     : https://prove2.me/theorems/9ec2a52e-54aa-50ac-8e8b-2c4d24b3ad13
-- title:
--   S3dx4: lam right
-- statement:
--   The S3dx4 construction uses the lam right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableEnormComposition.lean#L108-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableEnormComposition.lean#L108-L141

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

theorem Formalism.FourierDecayAlt.P.S3dx4.lam_right {e0 : Mx k r → ℂ} (he0 : Continuous e0) (γ : Mx k r) {z : Fin (2 * r + k + 1) → ℂ}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) [SigmaFinite μW] [SigmaFinite μN]
    (hz : Formalism.QuantumDeterminants.inWb k r z) (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    {h0 n0 : Mx k r} (hh0 : h0 ∈ Formalism.QuantumDeterminants.UWset k r z) (hn0 : n0 ∈ Formalism.QuantumDeterminants.Nset k r) (x y : Formalism.QuantumDeterminants.Mt k r) :
    abelian₂ e0 γ μp (μW.prod μN) x (fun i j => (h0 * n0 * Matrix.of y) i j) = abelian₂ e0 γ μp (μW.prod μN) x y := by sorry
