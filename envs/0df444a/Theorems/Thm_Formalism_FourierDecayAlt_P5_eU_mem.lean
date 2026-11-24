-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_eU_mem
-- name    : Formalism.FourierDecayAlt.P5.eU_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:25:12.03842+00:00
-- url     : https://prove2.me/theorems/5a72feb7-2273-484e-a257-29de64c655a2
-- title:
--   P5: e U mem
-- statement:
--   The P5 construction uses the e U mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMemMatrixAlgebra.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMemMatrixAlgebra.lean#L38-L44

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

theorem Formalism.FourierDecayAlt.P5.eU_mem (a : S) (i j : Fin 2) : (eU a i j : SlopeTestRemainingChoices S A) ∈ matSub C (Ix S) := by sorry
