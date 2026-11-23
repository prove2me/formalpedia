-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ioR_diag
-- name    : Formalism.FourierDecayAlt.P.Mx4.ioR_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:22.650482+00:00
-- url     : https://prove2.me/theorems/3e48e552-bade-41d5-95f6-3360b96ea855
-- title:
--   Mx4: io R diag
-- statement:
--   The Mx4 construction uses the io R diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L619-L625
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L619-L625

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

theorem Formalism.FourierDecayAlt.P.Mx4.ioR_diag (P : Par) (f : Ty P → ℝ) : ioR P (Matrix.diagonal f) = kap P fun π => ((f π : ℝ) : ℂ) := by sorry
