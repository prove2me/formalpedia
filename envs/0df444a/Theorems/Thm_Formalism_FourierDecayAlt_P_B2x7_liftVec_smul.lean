-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_liftVec_smul
-- name    : Formalism.FourierDecayAlt.P.B2x7.liftVec_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:58:17.729444+00:00
-- url     : https://prove2.me/theorems/6b3e37db-60dd-4df4-bf3b-771d62307529
-- title:
--   B2x7: lift Vec smul
-- statement:
--   The B2x7 construction uses the lift Vec smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationScalesHeisenbergMeasure.lean#L167-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationScalesHeisenbergMeasure.lean#L167-L173

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x7.liftVec_smul (c : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' (c • y) = c • liftVec k 1 r' y := by sorry
