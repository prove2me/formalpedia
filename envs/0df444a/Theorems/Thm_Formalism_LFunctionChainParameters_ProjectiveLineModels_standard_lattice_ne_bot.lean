-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_standard_lattice_ne_bot
-- name    : Formalism.LFunctionChainParameters.ProjectiveLineModels.standard_lattice_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:36:55.438077+00:00
-- url     : https://prove2.me/theorems/45f21aca-3432-46eb-882b-37e9c5d291f4
-- title:
--   Projective Line Models: standard lattice ne bot
-- statement:
--   The Projective Line Models construction uses the standard lattice ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L345-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L345-L351

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

theorem Formalism.LFunctionChainParameters.ProjectiveLineModels.standard_lattice_ne_bot (K n : Type) [Field K] [NumberField K] [Fintype n] [Nonempty n] :
    stdLat K n ≠ ⊥ := by sorry
