-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_smul_fnP
-- name    : Formalism.FourierDecayAlt.P.Mx4.smul_fnP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:51.773915+00:00
-- url     : https://prove2.me/theorems/fdf4d4ab-3a51-4534-aaa2-ed3320e6114b
-- title:
--   Mx4: smul fn P
-- statement:
--   The Mx4 construction uses the smul fn P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L141-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L141-L149

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

theorem Formalism.FourierDecayAlt.P.Mx4.smul_fnP (a : ℝ) (f fb : Fn r) : (a : ℂ) • fnP f fb = fnP ((a : ℂ) • f) ((a : ℂ) • fb) := by sorry
