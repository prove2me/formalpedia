-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_nab_step
-- name    : Formalism.FourierDecayAlt.P.Mx4.nab_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:04:14.010111+00:00
-- url     : https://prove2.me/theorems/39d707d1-a2e9-4a4f-bae4-d77bfa4be40b
-- title:
--   Mx4: nab step
-- statement:
--   The Mx4 construction uses the nab step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L756-L763
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean#L756-L763

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

theorem Formalism.FourierDecayAlt.P.Mx4.nab_step (a : ℝ) (D W : Pr r) (c : ℂ) :
    (D + ((a - 1 : ℝ) : ℂ) • W) * algebraMap ℂ (Pr r) c =
      algebraMap ℂ (Pr r) c * (D + (a : ℂ) • W) - W * algebraMap ℂ (Pr r) c := by sorry
