-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ioR_sR
-- name    : Formalism.FourierDecayAlt.P.Mx4.ioR_sR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:37.840523+00:00
-- url     : https://prove2.me/theorems/20366859-11d3-4333-bc7b-b49baed92385
-- title:
--   Mx4: io R s R
-- statement:
--   The Mx4 construction uses the io R s R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L611-L617
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L611-L617

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

theorem Formalism.FourierDecayAlt.P.Mx4.ioR_sR (P : Par) (l : ℕ) : ioR P (sR P l) = SS P l := by sorry
