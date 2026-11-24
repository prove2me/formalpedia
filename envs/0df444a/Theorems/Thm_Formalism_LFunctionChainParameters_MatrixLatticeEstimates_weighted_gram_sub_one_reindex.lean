-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_weighted_gram_sub_one_reindex
-- name    : Formalism.LFunctionChainParameters.MatrixLatticeEstimates.weighted_gram_sub_one_reindex
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:54.37368+00:00
-- url     : https://prove2.me/theorems/9351255d-6078-4255-ac5c-b0ddbc1de634
-- title:
--   Matrix Lattice Estimates: weighted gram sub one reindex
-- statement:
--   The Matrix Lattice Estimates construction uses the weighted gram sub one reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L93-L99

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

theorem Formalism.LFunctionChainParameters.MatrixLatticeEstimates.weighted_gram_sub_one_reindex {I α : Type} [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (i : I) :
    HilbertSchmidtNormSquare.Kd (toFin B) ga i - 1
      = Matrix.reindex (Fintype.equivFin (ι i)) (Fintype.equivFin (ι i)) (KdG B ga i - 1) := by sorry
