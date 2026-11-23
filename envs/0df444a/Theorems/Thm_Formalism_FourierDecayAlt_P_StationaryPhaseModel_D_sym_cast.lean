-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_sym_cast
-- name    : Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_sym_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:00.610735+00:00
-- url     : https://prove2.me/theorems/6ff93d89-87c3-48ba-b798-ed52eee88020
-- title:
--   Stationary Phase Model: D sym cast
-- statement:
--   The Stationary Phase Model construction uses the D sym cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1127-L1128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean#L1127-L1128

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

theorem Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_sym_cast {A : Set E} {w : E → ℝ} {m m' : ℤ} {N : ℕ} {K : ℝ} {f : E → F} (h : m = m')
    (hf : Sym A w m N K f) : Sym A w m' N K f := by sorry
