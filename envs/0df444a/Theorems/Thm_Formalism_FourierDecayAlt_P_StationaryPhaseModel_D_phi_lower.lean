-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_phi_lower
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_phi_lower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:41.807591+00:00
-- url     : https://prove2.me/theorems/adf550e0-84d8-4165-8992-1f17976713fe
-- title:
--   Stationary Phase Model: D phi lower
-- statement:
--   The Stationary Phase Model construction uses the D phi lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1381-L1417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1381-L1417

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_phi_lower (d : ℕ) (hd : 0 < d) (c : ℂ) (hc : c ≠ 0) (H : Matrix (Fin d) (Fin d) ℂ) (hs : H.IsSymm)
    (Γ : ℝ) (hΓ : 0 ≤ Γ) (hH : ∀ i j, ‖H i j‖ ≤ Γ) {Λ : ℝ} (hΛ : 0 < Λ)
    (hlow : ∀ x : Fin d → ℂ, ‖x‖ ≤ Λ * ‖H *ᵥ x‖) (x : Fin d → ℂ) :
    ∃ l : Fin d × Bool, ‖c‖ / (4 * Λ) * ‖x‖ ≤ |fderiv ℝ (D_phi d c H) x (dirv l)| := by sorry
