-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_hb_add_conj
-- name    : Formalism.FourierDecayAlt.P.B2x8.hb_add_conj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:57:09.794824+00:00
-- url     : https://prove2.me/theorems/39fd1e72-9520-451c-9dd1-9e6fe9d7fa0c
-- title:
--   B2x8: hb add conj
-- statement:
--   The B2x8 construction uses the hb add conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L283-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L283-L287

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

theorem Formalism.FourierDecayAlt.P.B2x8.hb_add_conj (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    hb k r' y s + conj (hb k r' y s) = - herm (Hpk k r') y y := by sorry
