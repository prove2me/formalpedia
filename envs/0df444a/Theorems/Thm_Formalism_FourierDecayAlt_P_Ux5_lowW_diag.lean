-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_lowW_diag
-- name    : Formalism.FourierDecayAlt.P.Ux5.lowW_diag
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:30:35.923056+00:00
-- url     : https://prove2.me/theorems/3c83d90b-b0e0-4a39-a5b9-6a589b5a9c72
-- title:
--   Ux5: low W diag
-- statement:
--   The Ux5 construction uses the low W diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L253-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L253-L254

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

theorem Formalism.FourierDecayAlt.P.Ux5.lowW_diag {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) (a : Fin p) : lowW σ v a a = 1 := by sorry
