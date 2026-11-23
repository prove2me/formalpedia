-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_phi_fderiv
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_phi_fderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:00.968697+00:00
-- url     : https://prove2.me/theorems/db6c6974-cab7-42d9-8a07-4808021f8246
-- title:
--   Stationary Phase Model: D phi fderiv
-- statement:
--   The Stationary Phase Model construction uses the D phi fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1362-L1373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1362-L1373

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_phi_fderiv (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (hs : H.IsSymm) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hH : ∀ i j, ‖H i j‖ ≤ Γ) : fderiv ℝ (D_phi d c H) = fun x => D_bilC d c H Γ hΓ hH x := by sorry
