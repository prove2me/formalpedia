-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_weighted_L2_add
-- name    : Formalism.FourierDecayAlt.P.LEx2.weighted_L2_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:56.878479+00:00
-- url     : https://prove2.me/theorems/c9adec8b-81c6-4c82-a980-31b441ac2365
-- title:
--   LEx2: weighted L2 add
-- statement:
--   The LEx2 construction uses the weighted L2 add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L70-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L70-L105

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

theorem Formalism.FourierDecayAlt.P.LEx2.weighted_L2_add (B : Base) (wt : B.Ω → ℝ) (hw : ∀ ω, 0 ≤ wt ω) (f g : B.Ω → ℂ) (hf : WeightedL2 B wt f)
    (hg : WeightedL2 B wt g) : WeightedL2 B wt (fun ω => f ω + g ω) := by sorry
