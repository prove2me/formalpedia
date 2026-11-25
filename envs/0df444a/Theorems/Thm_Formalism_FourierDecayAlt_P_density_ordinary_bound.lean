-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_density_ordinary_bound
-- name    : Formalism.FourierDecayAlt.P.density_ordinary_bound
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:29:36.202547+00:00
-- url     : https://prove2.me/theorems/2102659a-3a31-4b31-935c-7de7e8b8e10f
-- title:
--   P: density ordinary bound
-- statement:
--   The P construction uses the density ordinary bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L137-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L137-L177

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x5

theorem Formalism.FourierDecayAlt.P.density_ordinary_bound : Formalism.FourierDecayAlt.S3.DensOrdinaryBound := by sorry
