-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_zj_affine
-- name    : Formalism.FourierDecayAlt.P.Ux5.zj_affine
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:30:38.314359+00:00
-- url     : https://prove2.me/theorems/ed323c86-a129-4d5b-9de4-53ca25f2f7ca
-- title:
--   Ux5: zj affine
-- statement:
--   The Ux5 construction uses the zj affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L213-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L213-L218

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

theorem Formalism.FourierDecayAlt.P.Ux5.zj_affine {p s : ℕ} (a : Fin s → Fin p → ℂ) (b : Fin p → Fin s → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (CC : Matrix (Fin s) (Fin s) ℂ) :
    Zj a b H CC = blk2 H (H * Matrix.of b) (Matrix.of a * H) (Matrix.of a * H * Matrix.of b + CC) := by sorry
