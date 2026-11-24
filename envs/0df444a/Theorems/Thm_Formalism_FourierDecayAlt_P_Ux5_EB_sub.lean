-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_sub
-- name    : Formalism.FourierDecayAlt.P.Ux5.EB_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:23:09.099689+00:00
-- url     : https://prove2.me/theorems/99de1a6b-f27d-4dd4-a851-207a3c71bcd7
-- title:
--   Ux5: EB sub
-- statement:
--   The Ux5 construction uses the EB sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L40-L43

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

theorem Formalism.FourierDecayAlt.P.Ux5.EB_sub {m n : Type*} {A B : Matrix m n ℂ} {a b : ℝ} (hA : EB A a) (hB : EB B b) :
    EB (A - B) (a + b) := by sorry
