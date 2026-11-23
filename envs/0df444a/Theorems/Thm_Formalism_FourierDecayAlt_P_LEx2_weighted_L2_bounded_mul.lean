-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_weighted_L2_bounded_mul
-- name    : Formalism.FourierDecayAlt.P.LEx2.weighted_L2_bounded_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:56.580487+00:00
-- url     : https://prove2.me/theorems/264cfb35-62ce-4cf8-8f00-2b2017538bb3
-- title:
--   LEx2: weighted L2 bounded mul
-- statement:
--   The LEx2 construction uses the weighted L2 bounded mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L611-L619
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L611-L619

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem Formalism.FourierDecayAlt.P.LEx2.weighted_L2_bounded_mul (B : Base) (wt : B.Ω → ℝ) (hw : ∀ ω, 0 ≤ wt ω) (hwm : Measurable wt) (β f : B.Ω → ℂ) (C : ℝ)
    (hβm : Measurable β) (hβ : ∀ ω, ‖β ω‖ ≤ C) (hf : WeightedL2 B wt f) : WeightedL2 B wt (fun ω => β ω * f ω) := by sorry
