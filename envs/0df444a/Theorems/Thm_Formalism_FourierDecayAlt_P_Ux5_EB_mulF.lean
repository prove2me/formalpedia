-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mulF
-- name    : Formalism.FourierDecayAlt.P.Ux5.EB_mulF
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:50:41.432033+00:00
-- url     : https://prove2.me/theorems/93d01f53-7c20-41b7-9ba9-2211b3f377c7
-- title:
--   Ux5: EB mul F
-- statement:
--   The Ux5 construction uses the EB mul F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L700-L703
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L700-L703

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

theorem Formalism.FourierDecayAlt.P.Ux5.EB_mulF {l n : Type*} {m : ℕ} {A : Matrix l (Fin m) ℂ} {B : Matrix (Fin m) n ℂ} {a b : ℝ}
    (hA : EB A a) (hB : EB B b) : EB (A * B) ((m : ℝ) * (a * b)) := by sorry
