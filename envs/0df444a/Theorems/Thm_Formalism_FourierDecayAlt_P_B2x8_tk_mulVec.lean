-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_tk_mulVec
-- name    : Formalism.FourierDecayAlt.P.B2x8.tk_mulVec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:55:59.203099+00:00
-- url     : https://prove2.me/theorems/28ff85a8-a1fa-4ac0-9ebf-26f4a4423539
-- title:
--   B2x8: tk mul Vec
-- statement:
--   The B2x8 construction uses the tk mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L154-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L154-L161

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

theorem Formalism.FourierDecayAlt.P.B2x8.tk_mulVec (A : Mat k (1 + r')) (a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * (1 + r') + k + 1)) :
    (A *ᵥ mk3 k r' a y b) i = A i (tkF k r') * a + ∑ j, A i (levPos k 1 r' j) * y j + A i (tkL k r') * b := by sorry
