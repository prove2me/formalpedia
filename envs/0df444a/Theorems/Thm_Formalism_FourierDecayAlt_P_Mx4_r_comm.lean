-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_r_comm
-- name    : Formalism.FourierDecayAlt.P.Mx4.r_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:14.321823+00:00
-- url     : https://prove2.me/theorems/85499669-2e90-4075-a2df-f2617d969258
-- title:
--   Mx4: r comm
-- statement:
--   The Mx4 construction uses the r comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L703-L715
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L703-L715

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

theorem Formalism.FourierDecayAlt.P.Mx4.r_comm (P : Par) (hP : P.OK) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    sR P j * sR P l * Matrix.diagonal (fun π => rho P π j - rho P π l - 1) =
      sR P l * sR P j * Matrix.diagonal (fun π => rho P π j - rho P π l + 1) := by sorry
