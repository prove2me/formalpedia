-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_ioR_apply
-- name    : Formalism.FourierDecayAlt.P.Mx4.ioR_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:34.464656+00:00
-- url     : https://prove2.me/theorems/6fff2bbf-e86b-4815-ac3c-5751db2bd80a
-- title:
--   Mx4: io R apply
-- statement:
--   The Mx4 construction uses the io R apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L604-L605
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L604-L605

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

theorem Formalism.FourierDecayAlt.P.Mx4.ioR_apply (P : Par) (M : Matrix (Ty P) (Ty P) ℝ) (a b : Ty P) :
    ioR P M a b = algebraMap ℂ (Pr P.r) ((M a b : ℝ) : ℂ) := by sorry
