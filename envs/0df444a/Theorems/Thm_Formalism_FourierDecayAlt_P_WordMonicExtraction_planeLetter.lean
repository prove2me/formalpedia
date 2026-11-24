-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_planeLetter
-- name    : Formalism.FourierDecayAlt.P.WordMonicExtraction.planeLetter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:03.575677+00:00
-- url     : https://prove2.me/theorems/2e6adca3-28c2-4a4e-8ef2-a5c44dafbd7f
-- title:
--   Word Monic Extraction: plane Letter
-- statement:
--   The Word Monic Extraction construction uses the plane Letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L172-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordMonicExtraction.lean#L172-L203

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

theorem Formalism.FourierDecayAlt.P.WordMonicExtraction.planeLetter (Ξ : Sesq M) (n : ℕ) (D : Dat R) (x x' : M) (hS : Shape n D.A D.B)
    (hSv : Shape n D.Av D.Bv) :
    IsTopCoeff (fun Y => letterVal Ξ D Y x x') (2 * n) (D.s * Ξ x x') := by sorry
