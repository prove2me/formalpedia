-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_hasFDeriv_chart
-- name    : Formalism.FourierDecayAlt.P.Ux1.hasFDeriv_chart
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:10:14.757571+00:00
-- url     : https://prove2.me/theorems/e8c61bc6-77ad-41df-b133-9b9a95a759a9
-- title:
--   Ux1: has FDeriv chart
-- statement:
--   The Ux1 construction uses the has FDeriv chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L476-L510
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactlySupportedBanachModel.lean#L476-L510

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.Ux1.hasFDeriv_chart {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {H : Mat k r → E}
    (hH : CkOn ((1 : ℕ) : ℕ∞) (GV k r) H) {Y : J k r → ℝ} (hY : Y ∈ Dom k r) :
    HasFDerivAt (fun Y' => H (chart g0 Y'))
      (∑ i, (aC g0 i Y).smulRight (op true (Lt i) H (chart g0 Y))) Y := by sorry
