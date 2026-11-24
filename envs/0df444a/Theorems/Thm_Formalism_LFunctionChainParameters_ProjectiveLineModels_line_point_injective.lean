-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_line_point_injective
-- name    : Formalism.LFunctionChainParameters.ProjectiveLineModels.line_point_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:24.210486+00:00
-- url     : https://prove2.me/theorems/786e508d-9f6b-479d-90c0-316d52a9a189
-- title:
--   Projective Line Models: line point injective
-- statement:
--   The Projective Line Models construction uses the line point injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L110-L113

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

theorem Formalism.LFunctionChainParameters.ProjectiveLineModels.line_point_injective (i : Option (ZMod p) × ZMod p) : Function.Injective (linePt p i) := by sorry
