-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_vector_truncation_all_places
-- name    : Formalism.FourierDecayAlt.P.vector_truncation_all_places
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:47:45.423916+00:00
-- url     : https://prove2.me/theorems/9abd5e48-4124-5ba1-aba8-54ff4981bde4
-- title:
--   P: vector truncation all places
-- statement:
--   The P construction uses the vector truncation all places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L113-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TriangleInequalityAtPlace.lean#L113-L125

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open Formalism.FourierDecayAlt

theorem Formalism.FourierDecayAlt.P.vector_truncation_all_places : TBB.VecCutAll := by sorry
