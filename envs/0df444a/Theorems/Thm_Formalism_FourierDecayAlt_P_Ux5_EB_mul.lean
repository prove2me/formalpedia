-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mul
-- name    : Formalism.FourierDecayAlt.P.Ux5.EB_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:17:18.07583+00:00
-- url     : https://prove2.me/theorems/44690f2a-074f-4b23-9b8d-c12641f208d7
-- title:
--   Ux5: EB mul
-- statement:
--   The Ux5 construction uses the EB mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L16-L26

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

theorem Formalism.FourierDecayAlt.P.Ux5.EB_mul {l m n : Type*} [Fintype m] {A : Matrix l m ℂ} {B : Matrix m n ℂ} {a b : ℝ}
    (hA : EB A a) (hB : EB B b) : EB (A * B) (Fintype.card m * (a * b)) := by sorry
