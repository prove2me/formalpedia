-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_gg_ne
-- name    : Formalism.FourierDecayAlt.P.Mx4.gg_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:27.269641+00:00
-- url     : https://prove2.me/theorems/8bee0de3-4062-4e6e-9ec3-f71c6bec57e2
-- title:
--   Mx4: gg ne
-- statement:
--   The Mx4 construction uses the gg ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L135-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L135-L139

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

theorem Formalism.FourierDecayAlt.P.Mx4.gg_ne (TT : ℝ) : (gg TT : Fn r) ≠ 0 := by sorry
