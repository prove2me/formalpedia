-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TopDegreePolynomials_isTop_sub
-- name    : Formalism.FourierDecayAlt.P.TopDegreePolynomials.isTop_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:52.330743+00:00
-- url     : https://prove2.me/theorems/c5d05db6-a79a-4529-b9dd-356e5f3d297a
-- title:
--   Top Degree Polynomials: is Top sub
-- statement:
--   The Top Degree Polynomials construction uses the is Top sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDegreePolynomials.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDegreePolynomials.lean#L21-L26

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

theorem Formalism.FourierDecayAlt.P.TopDegreePolynomials.isTop_sub {W W' : ℝ → ℂ} {d : ℕ} {c c' : ℂ} (h : IsTopCoeff W d c)
    (h' : IsTopCoeff W' d c') : IsTopCoeff (fun Y => W Y - W' Y) d (c - c') := by sorry
