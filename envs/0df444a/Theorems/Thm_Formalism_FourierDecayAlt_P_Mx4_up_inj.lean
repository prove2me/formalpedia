-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_up_inj
-- name    : Formalism.FourierDecayAlt.P.Mx4.up_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:54:53.047351+00:00
-- url     : https://prove2.me/theorems/6e8b5ada-29e7-444e-b225-a52e30441830
-- title:
--   Mx4: up inj
-- statement:
--   The Mx4 construction uses the up inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L460-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L460-L462

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

theorem Formalism.FourierDecayAlt.P.Mx4.up_inj (P : Par) (l : ℕ) (π π1 π2 : Ty P) (h1 : Up P l π1 π) (h2 : Up P l π2 π) : π1 = π2 := by sorry
