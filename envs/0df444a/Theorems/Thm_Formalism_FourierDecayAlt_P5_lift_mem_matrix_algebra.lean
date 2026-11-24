-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_lift_mem_matrix_algebra
-- name    : Formalism.FourierDecayAlt.P5.lift_mem_matrix_algebra
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:41:18.608018+00:00
-- url     : https://prove2.me/theorems/16d01338-9f17-4dd4-bdcc-e22e90f03a44
-- title:
--   P5: lift mem matrix algebra
-- statement:
--   The P5 construction uses the lift mem matrix algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMemMatrixAlgebra.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMemMatrixAlgebra.lean#L54-L59

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMemMatrixAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {S : Type} [Fintype S] [DecidableEq S] (C : Subalgebra ℂ A)

theorem Formalism.FourierDecayAlt.P5.lift_mem_matrix_algebra {M : M2 A} (hM : ∀ i j, M i j ∈ C) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by sorry
