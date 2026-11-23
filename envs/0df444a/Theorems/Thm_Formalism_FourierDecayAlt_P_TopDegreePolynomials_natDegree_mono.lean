-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TopDegreePolynomials_natDegree_mono
-- name    : Formalism.FourierDecayAlt.P.TopDegreePolynomials.natDegree_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:37.276135+00:00
-- url     : https://prove2.me/theorems/efc5eec6-1d91-4b94-9794-5f7ca08b95eb
-- title:
--   Top Degree Polynomials: nat Degree mono
-- statement:
--   The Top Degree Polynomials construction uses the nat Degree mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDegreePolynomials.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopDegreePolynomials.lean#L34-L37

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

theorem Formalism.FourierDecayAlt.P.TopDegreePolynomials.natDegree_mono (h : ℂ) (i j : ℕ) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).natDegree = i + j := by sorry
