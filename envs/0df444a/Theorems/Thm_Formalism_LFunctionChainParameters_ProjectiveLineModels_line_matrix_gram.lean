-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_line_matrix_gram
-- name    : Formalism.LFunctionChainParameters.ProjectiveLineModels.line_matrix_gram
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:36:46.892796+00:00
-- url     : https://prove2.me/theorems/2f6da7f0-918f-452f-9b52-ab7eda7f904b
-- title:
--   Projective Line Models: line matrix gram
-- statement:
--   The Projective Line Models construction uses the line matrix gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L141-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L141-L145

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

theorem Formalism.LFunctionChainParameters.ProjectiveLineModels.line_matrix_gram (i j : Option (ZMod p) × ZMod p) :
    (lineMat p i)ᴴ * lineMat p j
      = Matrix.of fun t t' => if linePt p i t = linePt p j t' then (1 : ℂ) else 0 := by sorry
