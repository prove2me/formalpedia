-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_prod_zero
-- name    : Formalism.FourierDecayAlt.P.Mx4.prod_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:12.834847+00:00
-- url     : https://prove2.me/theorems/4247f233-95de-4791-848a-e44b1f0785dd
-- title:
--   Mx4: prod zero
-- statement:
--   The Mx4 construction uses the prod zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L694-L701
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L694-L701

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

theorem Formalism.FourierDecayAlt.P.Mx4.prod_zero {P : Par} {l j : ℕ} {π π2 : Ty P} (h : ¬ ∃ π1, Up P l π π1 ∧ Up P j π1 π2) :
    (sR P j * sR P l) π2 π = 0 := by sorry
