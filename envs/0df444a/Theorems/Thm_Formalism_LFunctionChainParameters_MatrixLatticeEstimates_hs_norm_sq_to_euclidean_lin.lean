-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_hs_norm_sq_to_euclidean_lin
-- name    : Formalism.LFunctionChainParameters.MatrixLatticeEstimates.hs_norm_sq_to_euclidean_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:17.49424+00:00
-- url     : https://prove2.me/theorems/5c6bec69-daa8-4059-8e6b-7dc71c19f75b
-- title:
--   Matrix Lattice Estimates: hs norm sq to euclidean lin
-- statement:
--   The Matrix Lattice Estimates construction uses the hs norm sq to euclidean lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/JointDModelAppliesUnitLattice.lean#L36-L38

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

theorem Formalism.LFunctionChainParameters.MatrixLatticeEstimates.hs_norm_sq_to_euclidean_lin (A : Matrix m n ℂ) : hs2 (Matrix.toEuclideanLin A) = hsSq A := by sorry
