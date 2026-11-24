-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_form_mulOp
-- name    : Formalism.FourierDecayAlt.P5.form_mulOp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:39:53.000159+00:00
-- url     : https://prove2.me/theorems/6517a6b6-0676-43f0-b46a-178864e8d8c2
-- title:
--   P5: form mul Op
-- statement:
--   The P5 construction uses the form mul Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMemMatrixAlgebra.lean#L189-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMemMatrixAlgebra.lean#L189-L201

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
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P5.form_mulOp (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (u y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    form μ l.succ (act (io (mkP Wv Wv')) u) y (Function.update c l t) =
      fsv s t * form μ l.succ u y (Function.update c l t) := by sorry
