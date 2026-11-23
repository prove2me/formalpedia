-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_symm_dot
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_symm_dot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:04.82791+00:00
-- url     : https://prove2.me/theorems/8b83387d-c782-417f-af37-fe4a9f44b2db
-- title:
--   Stationary Phase Model: D symm dot
-- statement:
--   The Stationary Phase Model construction uses the D symm dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1345-L1347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1345-L1347

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_symm_dot (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ) (hs : H.IsSymm) (x v : Fin d → ℂ) :
    v ⬝ᵥ (H *ᵥ x) = x ⬝ᵥ (H *ᵥ v) := by sorry
