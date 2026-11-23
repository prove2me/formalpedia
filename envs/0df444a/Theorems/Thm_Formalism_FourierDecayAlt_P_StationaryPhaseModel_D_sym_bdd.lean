-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_sym_bdd
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_sym_bdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:36.786412+00:00
-- url     : https://prove2.me/theorems/e281fcc7-682c-4cf9-ad3a-a269585908ba
-- title:
--   Stationary Phase Model: D sym bdd
-- statement:
--   The Stationary Phase Model construction uses the D sym bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1143-L1145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1143-L1145

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
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_sym_bdd {N : ℕ} {K : ℝ} {f : E → F} (hf : Sym Set.univ (fun _ : E => (1 : ℝ)) 0 N K f) :
    ∀ x, ∀ i ≤ N, ‖iteratedFDeriv ℝ i f x‖ ≤ K := by sorry
