-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_prod_expand
-- name    : Formalism.FourierDecayAlt.P.JFxE.prod_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:53.897752+00:00
-- url     : https://prove2.me/theorems/2f1d6d3d-27f1-4abf-8aae-7d24445acf72
-- title:
--   JFx E: prod expand
-- statement:
--   The JFx E construction uses the prod expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetRowsZero.lean#L131-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DetRowsZero.lean#L131-L146

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

theorem Formalism.FourierDecayAlt.P.JFxE.prod_expand {X : Type*} [Fintype X] :
    ∀ (t : ℕ) (c : Fin t → X → ℂ) (B : Fin t → X → A),
      (List.ofFn fun j => ∑ x, c j x • B j x).prod =
        ∑ φ : Fin t → X, (∏ j, c j (φ j)) • (List.ofFn fun j => B j (φ j)).prod := by sorry
