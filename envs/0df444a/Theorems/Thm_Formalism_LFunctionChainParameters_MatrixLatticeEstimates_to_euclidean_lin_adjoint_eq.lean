-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_to_euclidean_lin_adjoint_eq
-- name    : Formalism.LFunctionChainParameters.MatrixLatticeEstimates.to_euclidean_lin_adjoint_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:50:16.44757+00:00
-- url     : https://prove2.me/theorems/91f88640-7caa-4676-988e-4387e26c208d
-- title:
--   Matrix Lattice Estimates: to euclidean lin adjoint eq
-- statement:
--   The Matrix Lattice Estimates construction uses the to euclidean lin adjoint eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L32-L34

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
variable {m n o : Type} [Fintype m] [Fintype n] [Fintype o] [DecidableEq m] [DecidableEq n]
  [DecidableEq o]

theorem Formalism.LFunctionChainParameters.MatrixLatticeEstimates.to_euclidean_lin_adjoint_eq (A : Matrix m n ℂ) :
    LinearMap.adjoint (Matrix.toEuclideanLin A) = Matrix.toEuclideanLin Aᴴ := by sorry
