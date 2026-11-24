-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_hs_sq_one
-- name    : Formalism.LFunctionChainParameters.ProjectiveLineModels.hs_sq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:33.814061+00:00
-- url     : https://prove2.me/theorems/fd21081e-78ea-4757-b366-d1a131f639dd
-- title:
--   Projective Line Models: hs sq one
-- statement:
--   The Projective Line Models construction uses the hs sq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L332-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/ProjectiveLines.lean#L332-L334

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

theorem Formalism.LFunctionChainParameters.ProjectiveLineModels.hs_sq_one (n : Type) [Fintype n] [DecidableEq n] :
    hsSq (1 : Matrix n n ℂ) = Fintype.card n := by sorry
