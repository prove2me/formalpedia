-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_second_polynomial_third_of_parts
-- name    : Formalism.FourierDecayAlt.P.second_polynomial_third_of_parts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:51.675804+00:00
-- url     : https://prove2.me/theorems/e8c84a5d-6f1b-4792-824d-97b61791e06d
-- title:
--   P: second polynomial third of parts
-- statement:
--   The P construction uses the second polynomial third of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L318-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L318-L319

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

theorem Formalism.FourierDecayAlt.P.second_polynomial_third_of_parts : Formalism.FourierDecayAlt.PairingProductCorollary.LowerBlockNormalisedBoundFromComponents := by sorry
