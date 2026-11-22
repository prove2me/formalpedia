-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_multiplierPair_comm
-- name    : Formalism.FourierDecayAlt.P.Mx4.multiplierPair_comm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:42.94047+00:00
-- url     : https://prove2.me/theorems/9643e1ee-05a6-4b73-9d3e-0d81dcf49f7a
-- title:
--   Mx4: multiplier Pair comm
-- statement:
--   The Mx4 construction uses the multiplier Pair comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L88-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L88-L89

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

theorem Formalism.FourierDecayAlt.P.Mx4.multiplierPair_comm (f fb g gb : Fn r) : fnP f fb * fnP g gb = fnP g gb * fnP f fb := by sorry
