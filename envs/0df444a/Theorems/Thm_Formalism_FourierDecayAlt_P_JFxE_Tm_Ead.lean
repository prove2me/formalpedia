-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Tm_Ead
-- name    : Formalism.FourierDecayAlt.P.JFxE.Tm_Ead
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:54.127242+00:00
-- url     : https://prove2.me/theorems/1666a2ca-7fc2-44dc-89b3-5b8fda6aa60f
-- title:
--   JFx E: Tm Ead
-- statement:
--   The JFx E construction uses the Tm Ead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetRowsZero.lean#L116-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetRowsZero.lean#L116-L129

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

theorem Formalism.FourierDecayAlt.P.JFxE.Tm_Ead (E : Fin n → Fin n → A) {P Q : Matrix (Fin n) (Fin n) ℂ} (hQP : Q * P = 1) (v : ℂ) (c d : Fin n) :
    Tm (Ead E P Q) v c d = ∑ a, ∑ b, (P a c * Q d b) • Tm E v a b := by sorry
