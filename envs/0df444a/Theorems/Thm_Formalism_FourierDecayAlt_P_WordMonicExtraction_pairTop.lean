-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_pairTop
-- name    : Formalism.FourierDecayAlt.P.WordMonicExtraction.pairTop
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:55.131256+00:00
-- url     : https://prove2.me/theorems/f7d24624-074d-4684-9872-ab6476d30fba
-- title:
--   Word Monic Extraction: pair Top
-- statement:
--   The Word Monic Extraction construction uses the pair Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L128-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L128-L166

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

theorem Formalism.FourierDecayAlt.P.WordMonicExtraction.pairTop (Ξ : Sesq M) (P₁ P₂ : R[X]) (a b : ℕ) (h : ℝ) (X X' : M)
    (ha : P₁.natDegree ≤ a) (hb : P₂.natDegree ≤ b) :
    IsTopCoeff (fun Y => Ξ (evR P₁ Y • X) (evR P₂ (Y + h) • X')) (a + b)
      (Ξ (P₁.coeff a • X) (P₂.coeff b • X')) := by sorry
