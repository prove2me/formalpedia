-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_multiplierPair_add
-- name    : Formalism.FourierDecayAlt.P.Mx4.multiplierPair_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:31.775901+00:00
-- url     : https://prove2.me/theorems/13e7a09e-4c7e-4a66-bf41-7f5477f5abb8
-- title:
--   Mx4: multiplier Pair add
-- statement:
--   The Mx4 construction uses the multiplier Pair add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L77-L81

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

theorem Formalism.FourierDecayAlt.P.Mx4.multiplierPair_add (f fb g gb : Fn r) : fnP f fb + fnP g gb = fnP (f + g) (fb + gb) := by sorry
