-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_val_congr
-- name    : Formalism.FourierDecayAlt.P.Mx4.val_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:17.546278+00:00
-- url     : https://prove2.me/theorems/104010e5-95b3-44ed-92ed-5050a597cf6c
-- title:
--   Mx4: val congr
-- statement:
--   The Mx4 construction uses the val congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L280-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L280-L281

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

theorem Formalism.FourierDecayAlt.P.Mx4.val_congr (P : Par) (π : Ty P) (a b : Fin (P.k - 1)) (h : a = b) :
    ((π a : Fin _) : ℕ) = ((π b : Fin _) : ℕ) := by sorry
