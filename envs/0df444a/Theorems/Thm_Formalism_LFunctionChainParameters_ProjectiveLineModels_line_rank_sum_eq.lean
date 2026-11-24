-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_line_rank_sum_eq
-- name    : Formalism.LFunctionChainParameters.ProjectiveLineModels.line_rank_sum_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:28.542806+00:00
-- url     : https://prove2.me/theorems/8e7751d4-8f85-4980-bd15-f35c826b9d79
-- title:
--   Projective Line Models: line rank sum eq
-- statement:
--   The Projective Line Models construction uses the line rank sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L186-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L186-L188

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

theorem Formalism.LFunctionChainParameters.ProjectiveLineModels.line_rank_sum_eq : RsG (fun _ : Option (ZMod p) × ZMod p => ZMod p) = (p : ℝ) ^ 2 * ((p : ℝ) + 1) := by sorry
