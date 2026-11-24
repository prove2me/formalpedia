-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_lowW_entry
-- name    : Formalism.FourierDecayAlt.P.Ux5.lowW_entry
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:29:58.330058+00:00
-- url     : https://prove2.me/theorems/1baadcf4-d86a-4bd3-a5c1-10a68209f1c3
-- title:
--   Ux5: low W entry
-- statement:
--   The Ux5 construction uses the low W entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L256-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L256-L258

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

theorem Formalism.FourierDecayAlt.P.Ux5.lowW_entry {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) (q : LW σ) : lowW σ v q.1.1 q.1.2 = v q := by sorry
