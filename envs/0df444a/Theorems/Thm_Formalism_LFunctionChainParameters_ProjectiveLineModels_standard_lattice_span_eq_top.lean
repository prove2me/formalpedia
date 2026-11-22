-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_standard_lattice_span_eq_top
-- name    : Formalism.LFunctionChainParameters.ProjectiveLineModels.standard_lattice_span_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:17.276141+00:00
-- url     : https://prove2.me/theorems/3d835e91-cb8d-4d54-b9a0-16cd87157a74
-- title:
--   Projective Line Models: standard lattice span eq top
-- statement:
--   The Projective Line Models construction uses the standard lattice span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L101-L104

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

theorem Formalism.LFunctionChainParameters.ProjectiveLineModels.standard_lattice_span_eq_top (K n : Type) [Field K] [NumberField K] [Fintype n] :
    Submodule.span K ((stdLat K n : Submodule (𝓞 K) (n → K)) : Set (n → K)) = ⊤ := by sorry
