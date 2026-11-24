-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_line_map_ne_zero
-- name    : Formalism.LFunctionChainParameters.ProjectiveLineModels.line_map_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:12.566264+00:00
-- url     : https://prove2.me/theorems/4d52b839-b48e-41eb-9573-25eb25890123
-- title:
--   Projective Line Models: line map ne zero
-- statement:
--   The Projective Line Models construction uses the line map ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L192-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L192-L197

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
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]

theorem Formalism.LFunctionChainParameters.ProjectiveLineModels.line_map_ne_zero (i : Option (ZMod p) × ZMod p) : lineMap K p i ≠ 0 := by sorry
