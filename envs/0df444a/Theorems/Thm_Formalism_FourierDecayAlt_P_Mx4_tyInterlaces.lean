-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_tyInterlaces
-- name    : Formalism.FourierDecayAlt.P.Mx4.tyInterlaces
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:34.775794+00:00
-- url     : https://prove2.me/theorems/6a0d4bef-8ee1-41de-8aa9-c91c58179e95
-- title:
--   Mx4: ty Interlaces
-- statement:
--   The Mx4 construction uses the ty Interlaces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L240-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L240-L257

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}

theorem Formalism.FourierDecayAlt.P.Mx4.tyInterlaces : TyInterlaces := by sorry
