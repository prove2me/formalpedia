-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_L3
-- name    : Formalism.FourierDecayAlt.P.LEx1.L3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:10.361802+00:00
-- url     : https://prove2.me/theorems/a77a375e-9a71-4241-b52c-3519ac49139f
-- title:
--   LEx1: L3
-- statement:
--   The LEx1 construction uses the L3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L443-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2ConstMul.lean#L443-L476

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

theorem Formalism.FourierDecayAlt.P.LEx1.L3 (hC : E.CauchyTheta) (hCT : CutTheta) (hTS : ThetaSmooth) (hTR : ThetaRange) (B : Base) (c : Cut)
    (σ ε : ℝ) (h4 : 4 ≤ σ) (hε : 0 < ε) (p : ℕ) (h : B.Ω → ℂ) (hm : AEStronglyMeasurable h B.μ) (b : B.Ω → ℝ)
    (hb : Integrable b B.μ) (hbd : ∀ ω, th ε σ (B.G ω) * ‖h ω‖ ≤ b ω) :
    (∀ ε₂ : ℝ, 0 < ε₂ → Integrable (fun ω => (ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) * h ω) B.μ) ∧
    Tendsto (fun ε₂ : ℝ => ∫ ω, (ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) * h ω ∂B.μ) (𝓝[>] 0)
      (𝓝 (∫ ω, (ld p (th ε σ) (B.G ω) : ℂ) * h ω ∂B.μ)) := by sorry
