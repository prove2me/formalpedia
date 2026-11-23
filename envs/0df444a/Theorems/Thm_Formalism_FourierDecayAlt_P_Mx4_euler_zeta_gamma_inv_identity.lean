-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_euler_zeta_gamma_inv_identity
-- name    : Formalism.FourierDecayAlt.P.Mx4.euler_zeta_gamma_inv_identity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:59.695723+00:00
-- url     : https://prove2.me/theorems/0fdffe1a-14f4-4eb0-8351-7714bb84d154
-- title:
--   Mx4: euler zeta gamma inv identity
-- statement:
--   The Mx4 construction uses the euler zeta gamma inv identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L190-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L190-L197

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

theorem Formalism.FourierDecayAlt.P.Mx4.euler_zeta_gamma_inv_identity (TT : ℝ) : (coord vz)⁻¹ * euler vz (coord vz * (gg TT)⁻¹ : Fn r) =
    -(algebraMap ℂ (Fn r) (TT : ℂ) * ((gg TT)⁻¹ * (gg TT)⁻¹)) := by sorry
