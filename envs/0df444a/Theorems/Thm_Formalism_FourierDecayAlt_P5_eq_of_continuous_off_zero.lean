-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_eq_of_continuous_off_zero
-- name    : Formalism.FourierDecayAlt.P5.eq_of_continuous_off_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:53:39.804657+00:00
-- url     : https://prove2.me/theorems/bcc22ac3-98b2-53c3-9494-e0c76bc4a424
-- title:
--   P5: eq of continuous off zero
-- statement:
--   The P5 construction uses the eq of continuous off zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqOfContinuousOffZero.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqOfContinuousOffZero.lean#L52-L53

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqOfContinuousOffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

theorem Formalism.FourierDecayAlt.P5.eq_of_continuous_off_zero {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t, t ≠ 0 → f t = g t) : f = g := by sorry
