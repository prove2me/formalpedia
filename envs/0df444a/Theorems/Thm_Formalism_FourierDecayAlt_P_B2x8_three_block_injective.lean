-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_injective
-- name    : Formalism.FourierDecayAlt.P.B2x8.three_block_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:59:57.876806+00:00
-- url     : https://prove2.me/theorems/0436ebd2-d667-469f-a473-59e1bf9aed3b
-- title:
--   B2x8: three block injective
-- statement:
--   The B2x8 construction uses the three block injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L98-L103

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

theorem Formalism.FourierDecayAlt.P.B2x8.three_block_injective {a a' b b' : ℂ} {y y' : Fin (2 * r' + k + 1) → ℂ} (h : mk3 k r' a y b = mk3 k r' a' y' b') :
    a = a' ∧ y = y' ∧ b = b' := by sorry
