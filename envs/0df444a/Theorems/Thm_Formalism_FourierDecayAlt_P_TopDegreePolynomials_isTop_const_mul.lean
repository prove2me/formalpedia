-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TopDegreePolynomials_isTop_const_mul
-- name    : Formalism.FourierDecayAlt.P.TopDegreePolynomials.isTop_const_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:30.332084+00:00
-- url     : https://prove2.me/theorems/b9d3edd9-4b1f-494d-a576-af9272c71630
-- title:
--   Top Degree Polynomials: is Top const mul
-- statement:
--   The Top Degree Polynomials construction uses the is Top const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDegreePolynomials.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDegreePolynomials.lean#L28-L32

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TopDegreePolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7

theorem Formalism.FourierDecayAlt.P.TopDegreePolynomials.isTop_const_mul {W : ℝ → ℂ} {d : ℕ} {c : ℂ} (k : ℂ) (h : IsTopCoeff W d c) :
    IsTopCoeff (fun Y => k * W Y) d (k * c) := by sorry
