-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_eq_zero_of_sum_normSq_nonpos
-- name    : Formalism.FourierDecayAlt.P.FixedPointsGramVector.eq_zero_of_sum_normSq_nonpos
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:11:13.055865+00:00
-- url     : https://prove2.me/theorems/897cb209-2123-4ac8-ad1a-f97949ed2589
-- title:
--   Fixed Points Gram Vector: eq zero of sum norm Sq nonpos
-- statement:
--   The Fixed Points Gram Vector construction uses the eq zero of sum norm Sq nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FixedPointsGramVector.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FixedPointsGramVector.lean#L97-L102

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FixedPointsGramVector
open C2x5 C2x6 C2x7 HermitianProjections
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.FixedPointsGramVector.eq_zero_of_sum_normSq_nonpos {n : ℕ} (y : Fin n → ℂ) (h : ∑ i, Complex.normSq (y i) ≤ 0) : y = 0 := by sorry
