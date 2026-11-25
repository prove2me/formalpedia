-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_chebyshev_bound_attained
-- name    : Formalism.FourierDecayAlt.P.chebyshev_bound_attained
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:30:08.790292+00:00
-- url     : https://prove2.me/theorems/b7763135-7a58-5160-8c3c-7aac8b6612ee
-- title:
--   P: chebyshev bound attained
-- statement:
--   The P construction uses the chebyshev bound attained property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L393-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChebyshevExtremalPolynomials.lean#L393-L393

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.chebyshev_bound_attained : Formalism.FourierDecayAlt.F7.ChebAttained := by sorry
