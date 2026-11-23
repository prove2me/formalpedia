-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_prod_one
-- name    : Formalism.FourierDecayAlt.P.Mx4.prod_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:23.918259+00:00
-- url     : https://prove2.me/theorems/a479bdc4-9919-4391-a316-7fdd8a44a42d
-- title:
--   Mx4: prod one
-- statement:
--   The Mx4 construction uses the prod one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L688-L692
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L688-L692

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

theorem Formalism.FourierDecayAlt.P.Mx4.prod_one (P : Par) (l j : ℕ) (π π1 π2 : Ty P) (h1 : Up P l π π1) (h2 : Up P j π1 π2) :
    (sR P j * sR P l) π2 π = Real.sqrt (Nrm P j π1) * Real.sqrt (Nrm P l π) := by sorry
