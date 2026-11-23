-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_intersection_of_local
-- name    : Formalism.FourierDecayAlt.P.intersection_of_local
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:20.741995+00:00
-- url     : https://prove2.me/theorems/96daaea7-6288-4250-a3de-6e8157ceec72
-- title:
--   P: intersection of local
-- statement:
--   The P construction uses the intersection of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevToThreshold.lean#L77-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevToThreshold.lean#L77-L88

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevToThreshold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.intersection_of_local : Formalism.FourierDecayAlt.J.IntersectionOfLocal := by sorry
