-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dj_conj_mul
-- name    : Formalism.FourierDecayAlt.P.B2x8.dj_conj_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:00:42.28382+00:00
-- url     : https://prove2.me/theorems/44a533ca-5c43-4852-8b1c-84d90cef31b0
-- title:
--   B2x8: dj conj mul
-- statement:
--   The B2x8 construction uses the dj conj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1455-L1463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1455-L1463

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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x8.dj_conj_mul (a : Mat k r) (ha : IsUnit a.det) (p : Mt k r × Mt k r) :
    conjM a (mulM p) = mulM (conjM a p.1, conjM a p.2) := by sorry
