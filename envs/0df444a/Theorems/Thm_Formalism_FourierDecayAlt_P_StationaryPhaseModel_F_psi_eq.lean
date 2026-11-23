-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_psi_eq
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_psi_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:55.500568+00:00
-- url     : https://prove2.me/theorems/351f95c5-b9b1-4426-9e09-afab15f8947c
-- title:
--   Stationary Phase Model: F psi eq
-- statement:
--   The Stationary Phase Model construction uses the F psi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2909-L2912
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2909-L2912

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
variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ} {dg : (Fin d → ℂ) → Fin d → ℂ} {H : Matrix (Fin d) (Fin d) ℂ}

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_psi_eq (β : ℂ) {t : ℂ} (ht : t ≠ 0) (w : ℂ) :
    psi β (w / t) = Complex.exp (Complex.I * (((F_c β t * w).re / ‖t‖ : ℝ) : ℂ)) := by sorry
