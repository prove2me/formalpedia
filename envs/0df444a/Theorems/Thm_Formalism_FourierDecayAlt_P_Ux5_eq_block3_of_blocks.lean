-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_eq_block3_of_blocks
-- name    : Formalism.FourierDecayAlt.P.Ux5.eq_block3_of_blocks
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:31:02.371802+00:00
-- url     : https://prove2.me/theorems/b3fcdcbe-ad74-4237-a4c6-d62dcb72d270
-- title:
--   Ux5: eq block3 of blocks
-- statement:
--   The Ux5 construction uses the eq block3 of blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L582-L590
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L582-L590

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
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux5.eq_block3_of_blocks (M : B.Mat k (j + ρ)) :
    M = blk3 (bk M (q1 k ρ) (q1 k ρ)) (bk M (q1 k ρ) (q2 k j)) (bk M (q1 k ρ) (q3 k ρ))
      (bk M (q2 k j) (q1 k ρ)) (bk M (q2 k j) (q2 k j)) (bk M (q2 k j) (q3 k ρ))
      (bk M (q3 k ρ) (q1 k ρ)) (bk M (q3 k ρ) (q2 k j)) (bk M (q3 k ρ) (q3 k ρ)) := by sorry
