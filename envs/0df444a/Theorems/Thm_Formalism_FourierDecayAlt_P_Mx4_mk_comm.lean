-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_mk_comm
-- name    : Formalism.FourierDecayAlt.P.Mx4.mk_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:01.042326+00:00
-- url     : https://prove2.me/theorems/23ae2b25-ea28-4a51-a8a1-f1f5456399d7
-- title:
--   Mx4: mk comm
-- statement:
--   The Mx4 construction uses the mk comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L155-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L155-L158

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

theorem Formalism.FourierDecayAlt.P.Mx4.mk_comm (X Xs Y Ys : Op r) (h1 : X * Y = Y * X) (h2 : Xs * Ys = Ys * Xs) : mk X Xs * mk Y Ys = mk Y Ys * mk X Xs := by sorry
