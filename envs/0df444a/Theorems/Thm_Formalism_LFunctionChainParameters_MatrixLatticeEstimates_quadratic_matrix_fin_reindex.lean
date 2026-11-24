-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_quadratic_matrix_fin_reindex
-- name    : Formalism.LFunctionChainParameters.MatrixLatticeEstimates.quadratic_matrix_fin_reindex
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:40.417496+00:00
-- url     : https://prove2.me/theorems/96795f1e-c940-43c6-befd-352dbc65404f
-- title:
--   Matrix Lattice Estimates: quadratic matrix fin reindex
-- statement:
--   The Matrix Lattice Estimates construction uses the quadratic matrix fin reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L101-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L101-L109

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

theorem Formalism.LFunctionChainParameters.MatrixLatticeEstimates.quadratic_matrix_fin_reindex {I α : Type} [Fintype I] [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) :
    HilbertSchmidtNormSquare.Qm (toFin B) ga
      = Matrix.reindex (Fintype.equivFin α) (Fintype.equivFin α) (QmG B ga) := by sorry
