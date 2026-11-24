-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_line_model_input_sizes
-- name    : Formalism.LFunctionChainParameters.ProjectiveLineModels.line_model_input_sizes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:10.911837+00:00
-- url     : https://prove2.me/theorems/c91b2c22-0412-4de1-b8d8-b635145a9ea6
-- title:
--   Projective Line Models: line model input sizes
-- statement:
--   The Projective Line Models construction uses the line model input sizes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L171-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L171-L184

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
variable (p : ℕ) [Fact p.Prime]

theorem Formalism.LFunctionChainParameters.ProjectiveLineModels.line_model_input_sizes :
    InputSG (I := Option (ZMod p) × ZMod p) (ι := fun _ => ZMod p) (lineMat p) (fun _ => 1)
      ((p : ℝ) ^ 2) 0 0 0 := by sorry
