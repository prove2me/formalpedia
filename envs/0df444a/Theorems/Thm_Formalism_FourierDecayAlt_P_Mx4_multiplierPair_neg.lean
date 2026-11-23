-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_multiplierPair_neg
-- name    : Formalism.FourierDecayAlt.P.Mx4.multiplierPair_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:44.061799+00:00
-- url     : https://prove2.me/theorems/9984846e-0659-494b-98b5-e5d9939889f7
-- title:
--   Mx4: multiplier Pair neg
-- statement:
--   The Mx4 construction uses the multiplier Pair neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L86-L87

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

theorem Formalism.FourierDecayAlt.P.Mx4.multiplierPair_neg (f fb : Fn r) : -fnP f fb = fnP (-f) (-fb) := by sorry
