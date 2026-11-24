-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_det_permutationMatrix_ne_zero
-- name    : Formalism.FourierDecayAlt.P.Ux5.det_permutationMatrix_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:22:40.15157+00:00
-- url     : https://prove2.me/theorems/c234800a-3bad-4b7b-b2d3-97e06189f488
-- title:
--   Ux5: det permutation Matrix ne zero
-- statement:
--   The Ux5 construction uses the det permutation Matrix ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L241-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L241-L243

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

theorem Formalism.FourierDecayAlt.P.Ux5.det_permutationMatrix_ne_zero {p : ℕ} (σ : Equiv.Perm (Fin p)) : (wP σ).det ≠ 0 := by sorry
