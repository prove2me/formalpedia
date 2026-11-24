-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_weighted_frame_operator_to_lin
-- name    : Formalism.LFunctionChainParameters.MatrixLatticeEstimates.weighted_frame_operator_to_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:44.310857+00:00
-- url     : https://prove2.me/theorems/b64f3986-727a-45c1-b4ea-32f5af1a2dca
-- title:
--   Matrix Lattice Estimates: weighted frame operator to lin
-- statement:
--   The Matrix Lattice Estimates construction uses the weighted frame operator to lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L58-L64

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

theorem Formalism.LFunctionChainParameters.MatrixLatticeEstimates.weighted_frame_operator_to_lin {I α : Type} [Fintype I] [Fintype α] [DecidableEq α] {ι : I → Type}
    [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) :
    frQ ga (fun i => Matrix.toEuclideanLin (B i)) = Matrix.toEuclideanLin (QmG B ga) := by sorry
