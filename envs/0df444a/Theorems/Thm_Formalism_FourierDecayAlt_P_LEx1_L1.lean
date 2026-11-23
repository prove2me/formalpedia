-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_L1
-- name    : Formalism.FourierDecayAlt.P.LEx1.L1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:43.890933+00:00
-- url     : https://prove2.me/theorems/5e6f0209-3a54-463f-824c-3ca57424660e
-- title:
--   LEx1: L1
-- statement:
--   The LEx1 construction uses the L1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L302-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L302-L318

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

theorem Formalism.FourierDecayAlt.P.LEx1.L1 (hTR : ThetaRange) (hTL : ThetaLimit) (B : Base) (σ : ℝ) (hσ : 0 ≤ σ) (f : B.Ω → ℝ)
    (hf : Integrable f B.μ) :
    Tendsto (fun ε : ℝ => ∫ ω, th ε σ (B.G ω) * f ω ∂B.μ) (𝓝[>] 0) (𝓝 (∫ ω, f ω ∂B.μ)) := by sorry
