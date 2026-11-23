-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_L2
-- name    : Formalism.FourierDecayAlt.P.LEx1.L2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:09.621292+00:00
-- url     : https://prove2.me/theorems/99d34977-6220-4021-9678-3564560ff8ac
-- title:
--   LEx1: L2
-- statement:
--   The LEx1 construction uses the L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L320-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L320-L357

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem Formalism.FourierDecayAlt.P.LEx1.L2 (hTS : ThetaSmooth) (hTR : ThetaRange) (hTL : ThetaLimit) (hTB : ThetaBound) (hC : E.CauchyTheta)
    (B : Base) (σ : ℝ) (h4 : 4 ≤ σ) (p : ℕ) (hp : p ≠ 0) (h : B.Ω → ℂ) (hh : Integrable h B.μ) :
    Tendsto (fun ε : ℝ => ∫ ω, (ld p (th ε σ) (B.G ω) : ℂ) * h ω ∂B.μ) (𝓝[>] 0) (𝓝 0) := by sorry
