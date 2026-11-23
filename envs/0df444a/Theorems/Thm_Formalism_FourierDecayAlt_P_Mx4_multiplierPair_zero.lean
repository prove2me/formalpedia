-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_multiplierPair_zero
-- name    : Formalism.FourierDecayAlt.P.Mx4.multiplierPair_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:46.830121+00:00
-- url     : https://prove2.me/theorems/0cc0f5dd-3ff2-4d5d-aab7-31b2bf508111
-- title:
--   Mx4: multiplier Pair zero
-- statement:
--   The Mx4 construction uses the multiplier Pair zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L82-L85

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

theorem Formalism.FourierDecayAlt.P.Mx4.multiplierPair_zero : (fnP 0 0 : Pr r) = 0 := by sorry
