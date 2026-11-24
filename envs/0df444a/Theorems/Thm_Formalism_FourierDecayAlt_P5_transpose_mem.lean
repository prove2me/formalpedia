-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_transpose_mem
-- name    : Formalism.FourierDecayAlt.P5.transpose_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:41:38.637845+00:00
-- url     : https://prove2.me/theorems/707c02d0-e0e5-46a9-8a08-28f5dbfb58e8
-- title:
--   P5: transpose mem
-- statement:
--   The P5 construction uses the transpose mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMemMatrixAlgebra.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMemMatrixAlgebra.lean#L67-L69

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

theorem Formalism.FourierDecayAlt.P5.transpose_mem {n : Type} [Fintype n] [DecidableEq n] {C' : Subalgebra ℂ A} {M : Matrix n n A}
    (hM : M ∈ matSub C' n) : Mᵀ ∈ matSub C' n := by sorry
