-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_p3bOfA_ok
-- name    : Formalism.FourierDecayAlt.P.SecondPolynomialClauses.p3bOfA_ok
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:25.38709+00:00
-- url     : https://prove2.me/theorems/a4ff4167-2c93-4b9a-8e06-271e8dc423c4
-- title:
--   Second Polynomial Clauses: p3b Of A ok
-- statement:
--   The Second Polynomial Clauses construction uses the p3b Of A ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L12-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L12-L51

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

theorem Formalism.FourierDecayAlt.P.SecondPolynomialClauses.p3bOfA_ok : LeadingBlockBoundFromRecursion := by sorry
