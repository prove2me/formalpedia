-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_inclusion_matrix_isometry
-- name    : Formalism.LFunctionChainParameters.ProjectiveLineModels.inclusion_matrix_isometry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:05.212062+00:00
-- url     : https://prove2.me/theorems/b5354d0d-0f14-436e-bc9f-64438d5d2f5d
-- title:
--   Projective Line Models: inclusion matrix isometry
-- statement:
--   The Projective Line Models construction uses the inclusion matrix isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L327-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L327-L330

import Definitions.Def_Formalism_SizeWindowBrackets_JointDPublishedSizes
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ProjectiveLineModels
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
open Formalism.LFunctionChainParameters.MatrixLatticeEstimates

theorem Formalism.LFunctionChainParameters.ProjectiveLineModels.inclusion_matrix_isometry (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁] :
    (inclMat κ κ₁)ᴴ * inclMat κ κ₁ = 1 := by sorry
