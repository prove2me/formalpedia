-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_qminor_Ead
-- name    : Formalism.FourierDecayAlt.P.JFxE.qminor_Ead
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:19.762181+00:00
-- url     : https://prove2.me/theorems/fdb55f02-f1df-405e-a6f9-826e53298c21
-- title:
--   JFx E: qminor Ead
-- statement:
--   The JFx E construction uses the qminor Ead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetRowsZero.lean#L189-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetRowsZero.lean#L189-L252

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

theorem Formalism.FourierDecayAlt.P.JFxE.qminor_Ead (E : Fin n → Fin n → A) {P Q : Matrix (Fin n) (Fin n) ℂ} (hQP : Q * P = 1) {t : ℕ}
    (e : Fin t ≃ Fin n) (u : ℂ) :
    qminor (Ead E P Q) e e u = P.det • ∑ β : Fin t → Fin n, (∏ j, Q (e j) (β j)) • qminor E e β u := by sorry
