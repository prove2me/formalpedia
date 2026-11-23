-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_mulOp_add
-- name    : Formalism.FourierDecayAlt.P.Mx4.mulOp_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:04:06.968835+00:00
-- url     : https://prove2.me/theorems/532718f0-4088-4482-849a-b2cfb02cff70
-- title:
--   Mx4: mul Op add
-- statement:
--   The Mx4 construction uses the mul Op add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L68-L69

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

theorem Formalism.FourierDecayAlt.P.Mx4.mulOp_add (f g : Fn r) : mulOp f + mulOp g = mulOp (f + g) := by sorry
