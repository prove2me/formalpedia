-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_det_rows_zero
-- name    : Formalism.FourierDecayAlt.P.JFxE.det_rows_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:01.752962+00:00
-- url     : https://prove2.me/theorems/ea794178-40ff-4953-8197-bd9b57f95e66
-- title:
--   JFx E: det rows zero
-- statement:
--   The JFx E construction uses the det rows zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetRowsZero.lean#L163-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetRowsZero.lean#L163-L167

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem Formalism.FourierDecayAlt.P.JFxE.det_rows_zero {t : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (e : Fin t ≃ Fin n) (α : Fin t → Fin n)
    (hα : ¬ Function.Injective α) : (Matrix.of fun i j : Fin t => P (α i) (e j)).det = 0 := by sorry
