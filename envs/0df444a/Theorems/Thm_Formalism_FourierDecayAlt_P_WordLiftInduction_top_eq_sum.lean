-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordLiftInduction_top_eq_sum
-- name    : Formalism.FourierDecayAlt.P.WordLiftInduction.top_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:55.486611+00:00
-- url     : https://prove2.me/theorems/66c0ff68-645c-4522-b03d-d5bff4627d4b
-- title:
--   Word Lift Induction: top eq sum
-- statement:
--   The Word Lift Induction construction uses the top eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordLiftInduction.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordLiftInduction.lean#L9-L24

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordLiftInduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordLiftInduction
open Finset Polynomial Formalism.FourierDecayAlt.F7

theorem Formalism.FourierDecayAlt.P.WordLiftInduction.top_eq_sum {W : ℝ → ℂ} {d : ℕ} {c : ℂ} (h : IsTopCoeff W d c) (y : Fin (d + 1) → ℝ)
    (hy : Function.Injective y) : ∑ j, ((lagCo y j : ℝ) : ℂ) * W (y j) = c := by sorry
