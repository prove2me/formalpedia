-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_lev_mul
-- name    : Formalism.FourierDecayAlt.P.B2x8.al_lev_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:59:21.566203+00:00
-- url     : https://prove2.me/theorems/853472e6-4098-437b-949e-77cb8064427c
-- title:
--   B2x8: al lev mul
-- statement:
--   The B2x8 construction uses the al lev mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L935-L938
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L935-L938

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x8.al_lev_mul (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by sorry
