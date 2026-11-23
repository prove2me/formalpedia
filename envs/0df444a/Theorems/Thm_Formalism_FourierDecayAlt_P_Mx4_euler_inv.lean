-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_euler_inv
-- name    : Formalism.FourierDecayAlt.P.Mx4.euler_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:37.451423+00:00
-- url     : https://prove2.me/theorems/10304953-d8fb-4921-8e05-d6ba90473fb1
-- title:
--   Mx4: euler inv
-- statement:
--   The Mx4 construction uses the euler inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L108-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L108-L114

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

theorem Formalism.FourierDecayAlt.P.Mx4.euler_inv (v : Var r) (f : Fn r) (hf : f ≠ 0) : euler v f⁻¹ = -(f⁻¹ * f⁻¹ * euler v f) := by sorry
