-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_mulOp_mul
-- name    : Formalism.FourierDecayAlt.P.Mx4.mulOp_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:04.819835+00:00
-- url     : https://prove2.me/theorems/1b99fb24-225d-4fec-b9b7-e7f72a19128e
-- title:
--   Mx4: mul Op mul
-- statement:
--   The Mx4 construction uses the mul Op mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L66-L67

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

theorem Formalism.FourierDecayAlt.P.Mx4.mulOp_mul (f g : Fn r) : mulOp f * mulOp g = mulOp (f * g) := by sorry
