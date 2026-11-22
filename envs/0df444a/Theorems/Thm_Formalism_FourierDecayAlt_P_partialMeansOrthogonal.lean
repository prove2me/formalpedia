-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_partialMeansOrthogonal
-- name    : Formalism.FourierDecayAlt.P.partialMeansOrthogonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:39.356001+00:00
-- url     : https://prove2.me/theorems/c68c9eb2-364f-429a-9f39-5f4f452329f7
-- title:
--   P: partial Means Orthogonal
-- statement:
--   The P construction uses the partial Means Orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialMeansOrthogonal.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PartialMeansOrthogonal.lean#L36-L39

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialMeansOrthogonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.partialMeansOrthogonal : Formalism.FourierDecayAlt.A6.POrth := by sorry
