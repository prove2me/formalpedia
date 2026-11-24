-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_Tl_mp
-- name    : Formalism.FourierDecayAlt.P.B2x8.Tl_mp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:58:30.940259+00:00
-- url     : https://prove2.me/theorems/bdf11193-29ed-4d87-a46f-bde3cd18550c
-- title:
--   B2x8: Tl mp
-- statement:
--   The B2x8 construction uses the Tl mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L661-L667
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L661-L667

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

theorem Formalism.FourierDecayAlt.P.B2x8.Tl_mp (g₁ : Mat k r') (hg : g₁ ∈ GV k r') :
    MeasurePreserving (Tl k r' g₁) (μx.prod (volume : Measure (HPar k r'))) (μx.prod (volume : Measure (HPar k r'))) := by sorry
