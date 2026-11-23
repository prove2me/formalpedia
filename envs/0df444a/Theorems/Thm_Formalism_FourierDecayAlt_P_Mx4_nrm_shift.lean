-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_nrm_shift
-- name    : Formalism.FourierDecayAlt.P.Mx4.nrm_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:10.639728+00:00
-- url     : https://prove2.me/theorems/f8b7e4dd-e000-4ebc-be46-2924e4b32bc4
-- title:
--   Mx4: nrm shift
-- statement:
--   The Mx4 construction uses the nrm shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L503-L541
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L503-L541

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

theorem Formalism.FourierDecayAlt.P.Mx4.nrm_shift (P : Par) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l)
    (π πj : Ty P) (hU : Up P j π πj) (hp : rho P π j - rho P π l + 1 ≠ 0) (hm : rho P π j - rho P π l - 1 ≠ 0) :
    Nrm P l πj * (rho P π j - rho P π l + 1) = Nrm P l π * (rho P π j - rho P π l - 1) := by sorry
