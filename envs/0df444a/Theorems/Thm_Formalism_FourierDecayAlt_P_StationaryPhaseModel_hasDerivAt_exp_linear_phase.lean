-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_hasDerivAt_exp_linear_phase
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.hasDerivAt_exp_linear_phase
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:15.625601+00:00
-- url     : https://prove2.me/theorems/13ac4140-01eb-403e-9e32-4772265c6457
-- title:
--   Stationary Phase Model: has Deriv At exp linear phase
-- statement:
--   The Stationary Phase Model construction uses the has Deriv At exp linear phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1623-L1632
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1623-L1632

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
variable {d : ℕ} {β : ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.hasDerivAt_exp_linear_phase (a p τ s : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * (((a + s * p) / τ : ℝ) : ℂ)))
      ((Complex.I * ((p / τ : ℝ) : ℂ)) * Complex.exp (Complex.I * (((a + s * p) / τ : ℝ) : ℂ))) s := by sorry
