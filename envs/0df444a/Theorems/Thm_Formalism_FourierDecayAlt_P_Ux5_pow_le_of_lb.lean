-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_pow_le_of_lb
-- name    : Formalism.FourierDecayAlt.P.Ux5.pow_le_of_lb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:29:08.491732+00:00
-- url     : https://prove2.me/theorems/30fcb3c6-242f-470f-8474-1eef70359b93
-- title:
--   Ux5: pow le of lb
-- statement:
--   The Ux5 construction uses the pow le of lb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L97-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L97-L106

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

theorem Formalism.FourierDecayAlt.P.Ux5.pow_le_of_lb {m δ : ℝ} {e q : ℕ} (hm : 0 ≤ m) (hδ : 0 < δ) (hq : δ ≤ m ^ q) (he : e ≤ q) :
    m ^ e ≤ (1 + δ⁻¹) * m ^ q := by sorry
