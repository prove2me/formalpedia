-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_weighted_L2_sum
-- name    : Formalism.FourierDecayAlt.P.LEx2.weighted_L2_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:53:47.066521+00:00
-- url     : https://prove2.me/theorems/ab7335c1-278e-4e5c-9ad3-1b5d7ea35659
-- title:
--   LEx2: weighted L2 sum
-- statement:
--   The LEx2 construction uses the weighted L2 sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L107-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedL2BoundedMul.lean#L107-L115

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

theorem Formalism.FourierDecayAlt.P.LEx2.weighted_L2_sum (B : Base) (wt : B.Ω → ℝ) (hw : ∀ ω, 0 ≤ wt ω) {I : Type} (s : Finset I) (f : I → B.Ω → ℂ)
    (hf : ∀ i ∈ s, WeightedL2 B wt (f i)) : WeightedL2 B wt (fun ω => ∑ i ∈ s, f i ω) := by sorry
