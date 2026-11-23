-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_Pe_iterated
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_Pe_iterated
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:40.025813+00:00
-- url     : https://prove2.me/theorems/347147aa-eb28-409d-82e8-474a6579d6e8
-- title:
--   Stationary Phase Model: E Pe iterated
-- statement:
--   The Stationary Phase Model construction uses the E Pe iterated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1944-L1956
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1944-L1956

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_Pe_iterated {φ : E → ℝ} {n : ℕ} (hφ : ContDiff ℝ n φ) {i : ℕ} (hi : i ≤ n) (x : E) :
    iteratedFDeriv ℝ i (E_Pe φ) x =
      (1 / 2 : ℝ) • (iteratedFDeriv ℝ i (E_P φ) x + (-1 : ℝ) ^ i • iteratedFDeriv ℝ i (E_P φ) (-x)) := by sorry
