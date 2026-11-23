-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_second_polynomial_first_clause
-- name    : Formalism.FourierDecayAlt.P.SecondPolynomialClauses.second_polynomial_first_clause
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:14.367164+00:00
-- url     : https://prove2.me/theorems/f39a82be-4379-4868-9f82-9a09e40b4b6a
-- title:
--   Second Polynomial Clauses: second polynomial first clause
-- statement:
--   The Second Polynomial Clauses construction uses the second polynomial first clause property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L96-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L96-L106

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SecondPolynomialClauses
open Formalism.FourierDecayAlt.PairingProductCorollary

theorem Formalism.FourierDecayAlt.P.SecondPolynomialClauses.second_polynomial_first_clause : PairingGramBound := by sorry
