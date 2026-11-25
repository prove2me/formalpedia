-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_upper_splitting_of_lower
-- name    : Formalism.FourierDecayAlt.P.upper_splitting_of_lower
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:43:33.835379+00:00
-- url     : https://prove2.me/theorems/f059e71b-8cec-533d-a74e-dfa1cb2e31f9
-- title:
--   P: upper splitting of lower
-- statement:
--   The P construction uses the upper splitting of lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L232-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean#L232-L249

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2

theorem Formalism.FourierDecayAlt.P.upper_splitting_of_lower : C2.UpSplitOfLowSplit := by sorry
