-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_bk
-- name    : Formalism.FourierDecayAlt.P.Ux5.EB_bk
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:30:21.445017+00:00
-- url     : https://prove2.me/theorems/9a33ff49-7994-416f-92cb-e23d853561ad
-- title:
--   Ux5: EB bk
-- statement:
--   The Ux5 construction uses the EB bk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L640-L642
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L640-L642

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

theorem Formalism.FourierDecayAlt.P.Ux5.EB_bk {k j ρ : ℕ} {ι κ : Type*} (M : B.Mat k (j + ρ)) (f : ι → Ix k j ρ) (f' : κ → Ix k j ρ) :
    EB (bk M f f') (B.gN M) := by sorry
