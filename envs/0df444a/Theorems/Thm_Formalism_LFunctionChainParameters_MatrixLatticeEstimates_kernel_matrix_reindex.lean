-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_kernel_matrix_reindex
-- name    : Formalism.LFunctionChainParameters.MatrixLatticeEstimates.kernel_matrix_reindex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:10.044024+00:00
-- url     : https://prove2.me/theorems/97ecf294-486a-4899-bd87-0000f5fa0502
-- title:
--   Matrix Lattice Estimates: kernel matrix reindex
-- statement:
--   The Matrix Lattice Estimates construction uses the kernel matrix reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L85-L91

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

theorem Formalism.LFunctionChainParameters.MatrixLatticeEstimates.kernel_matrix_reindex {I α : Type} [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (i j : I) :
    HilbertSchmidtNormSquare.Kp (toFin B) ga i j
      = Matrix.reindex (Fintype.equivFin (ι i)) (Fintype.equivFin (ι j)) (KpG B ga i j) := by sorry
