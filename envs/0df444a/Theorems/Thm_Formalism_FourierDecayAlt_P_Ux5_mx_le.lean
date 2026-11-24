-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_mx_le
-- name    : Formalism.FourierDecayAlt.P.Ux5.mx_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:58:59.928169+00:00
-- url     : https://prove2.me/theorems/06f2eb75-687b-4274-bdbd-4a061a5472ae
-- title:
--   Ux5: mx le
-- statement:
--   The Ux5 construction uses the mx le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L64-L68

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

theorem Formalism.FourierDecayAlt.P.Ux5.mx_le {m n : Type*} [Fintype m] [Fintype n] {A : Matrix m n ℂ} {c : ℝ} (h : EB A c) (hc : 0 ≤ c) :
    mx A ≤ c := by sorry
