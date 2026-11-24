-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_kc_sum
-- name    : Formalism.FourierDecayAlt.P.Ux1.kc_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:10:40.858795+00:00
-- url     : https://prove2.me/theorems/349ec508-a49a-4304-912b-c3d1c213f3d6
-- title:
--   Ux1: kc sum
-- statement:
--   The Ux1 construction uses the kc sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L336-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L336-L339

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux1.kc_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Z : ι → Mat k r) (i : J k r) :
    kc i (∑ b ∈ s, c b • Z b) = ∑ b ∈ s, c b * kc i (Z b) := by sorry
