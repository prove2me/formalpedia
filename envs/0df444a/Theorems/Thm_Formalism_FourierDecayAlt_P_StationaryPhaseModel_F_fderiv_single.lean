-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_fderiv_single
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_fderiv_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:00.898862+00:00
-- url     : https://prove2.me/theorems/06da6f18-ed12-4eba-a4d5-c7d0ec4a60b9
-- title:
--   Stationary Phase Model: F fderiv single
-- statement:
--   The Stationary Phase Model construction uses the F fderiv single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2571-L2577
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L2571-L2577

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_fderiv_single {d : ℕ} {g : (Fin d → ℂ) → ℂ} {x : Fin d → ℂ} {k : Fin d} {D : ℂ}
    (hg : DifferentiableAt ℂ g x) (h : HasDerivAt (fun ξ => g (Function.update x k ξ)) D (x k)) :
    fderiv ℂ g x (Pi.single k 1) = D := by sorry
