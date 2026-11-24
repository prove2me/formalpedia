-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_entry_le_gN
-- name    : Formalism.FourierDecayAlt.P.Ux5.entry_le_gN
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:05:34.141141+00:00
-- url     : https://prove2.me/theorems/1fabd1d3-6dda-4470-8007-0c4a0bc45ed7
-- title:
--   Ux5: entry le g N
-- statement:
--   The Ux5 construction uses the entry le g N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L614-L624
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L614-L624

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

theorem Formalism.FourierDecayAlt.P.Ux5.entry_le_gN {k r : ℕ} (M : B.Mat k r) (i j : Fin (2 * r + k + 1)) : ‖M i j‖ ≤ B.gN M := by sorry
