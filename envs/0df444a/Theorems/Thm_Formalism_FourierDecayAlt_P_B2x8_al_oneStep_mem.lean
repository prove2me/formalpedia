-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_oneStep_mem
-- name    : Formalism.FourierDecayAlt.P.B2x8.al_oneStep_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:57:55.560195+00:00
-- url     : https://prove2.me/theorems/4d04c81c-fe83-497c-90ee-9d68db9bd37c
-- title:
--   B2x8: al one Step mem
-- statement:
--   The B2x8 construction uses the al one Step mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1039-L1042
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1039-L1042

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

theorem Formalism.FourierDecayAlt.P.B2x8.al_oneStep_mem (x x' : HPar k r') {c : ℂ} (hc : c ≠ 0) {g₁ : Mat k r'} (hg : g₁ ∈ GV k r') :
    oneStep k r' x c g₁ x' ∈ GV k (1 + r') := by sorry
