-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_p2cOfParts_ok
-- name    : Formalism.FourierDecayAlt.P.SecondPolynomialClauses.p2cOfParts_ok
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:10.539615+00:00
-- url     : https://prove2.me/theorems/d4982965-8922-4ee4-aa87-d52f049b30d0
-- title:
--   Second Polynomial Clauses: p2c Of Parts ok
-- statement:
--   The Second Polynomial Clauses construction uses the p2c Of Parts ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L213-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L213-L306

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

theorem Formalism.FourierDecayAlt.P.SecondPolynomialClauses.p2cOfParts_ok : LowerBlockNormalisedBoundFromComponents := by sorry
