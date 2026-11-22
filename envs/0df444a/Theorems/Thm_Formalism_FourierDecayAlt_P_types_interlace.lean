-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_types_interlace
-- name    : Formalism.FourierDecayAlt.P.types_interlace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:19:31.750492+00:00
-- url     : https://prove2.me/theorems/2b8fed8f-6e5a-4bee-b166-65e0f4188307
-- title:
--   P: types interlace
-- statement:
--   The P construction uses the types interlace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L413-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/InterlaceSignTwo.lean#L413-L413

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.types_interlace : Formalism.FourierDecayAlt.M.TyInterlaces := by sorry
