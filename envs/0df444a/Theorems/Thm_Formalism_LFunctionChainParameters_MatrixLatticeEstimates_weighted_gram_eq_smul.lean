-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_weighted_gram_eq_smul
-- name    : Formalism.LFunctionChainParameters.MatrixLatticeEstimates.weighted_gram_eq_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:21.932258+00:00
-- url     : https://prove2.me/theorems/33112065-b677-43d5-ae94-6dbaf5221953
-- title:
--   Matrix Lattice Estimates: weighted gram eq smul
-- statement:
--   The Matrix Lattice Estimates construction uses the weighted gram eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L48-L51

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.MatrixLatticeEstimates
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)

theorem Formalism.LFunctionChainParameters.MatrixLatticeEstimates.weighted_gram_eq_smul {I α : Type} [Fintype α] {ι : I → Type} (B : ∀ i, Matrix α (ι i) ℂ)
    (ga : I → ℝ) (i : I) (hi : 0 ≤ ga i) : KdG B ga i = ((ga i : ℝ) : ℂ) • ((B i)ᴴ * B i) := by sorry
