-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_lowW_lower
-- name    : Formalism.FourierDecayAlt.P.Ux5.lowW_lower
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:30:21.405304+00:00
-- url     : https://prove2.me/theorems/9392a7a0-de8e-4d4f-aab3-795cdd612231
-- title:
--   Ux5: low W lower
-- statement:
--   The Ux5 construction uses the low W lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L249-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L249-L251

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5

theorem Formalism.FourierDecayAlt.P.Ux5.lowW_lower {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) (a b : Fin p) (h : a < b) : lowW σ v a b = 0 := by sorry
