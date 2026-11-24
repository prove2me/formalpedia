-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_hs_sq_reindex
-- name    : Formalism.LFunctionChainParameters.MatrixLatticeEstimates.hs_sq_reindex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:24.042143+00:00
-- url     : https://prove2.me/theorems/0391db43-6dd7-4da8-9288-ed16c245334d
-- title:
--   Matrix Lattice Estimates: hs sq reindex
-- statement:
--   The Matrix Lattice Estimates construction uses the hs sq reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L71-L77

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

theorem Formalism.LFunctionChainParameters.MatrixLatticeEstimates.hs_sq_reindex {m n m' n' : Type} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    (e : m ≃ m') (f : n ≃ n') (M : Matrix m n ℂ) : hsSq (Matrix.reindex e f M) = hsSq M := by sorry
