-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_det_rows_perm
-- name    : Formalism.FourierDecayAlt.P.JFxE.det_rows_perm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:00.21374+00:00
-- url     : https://prove2.me/theorems/44d1127b-ad2f-4f16-90d7-87bf302f68b8
-- title:
--   JFx E: det rows perm
-- statement:
--   The JFx E construction uses the det rows perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetRowsZero.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetRowsZero.lean#L157-L161

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

theorem Formalism.FourierDecayAlt.P.JFxE.det_rows_perm {t : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (e : Fin t ≃ Fin n) (γ : Equiv.Perm (Fin t)) :
    (Matrix.of fun i j : Fin t => P (e (γ i)) (e j)).det = ((Equiv.Perm.sign γ : ℤ) : ℂ) * P.det := by sorry
