-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_dense_fcoord
-- name    : Formalism.IndefR.LatticeTransfer.BlockMetrics.dense_fcoord
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:48.61951+00:00
-- url     : https://prove2.me/theorems/191c8641-865a-41fe-b882-53e549e418e3
-- title:
--   Block Metrics: dense fcoord
-- statement:
--   The Block Metrics construction uses the dense fcoord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean#L131-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean#L131-L157

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.BlockMetrics

theorem Formalism.IndefR.LatticeTransfer.BlockMetrics.dense_fcoord {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    DenseRange fun x : V => (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι) := by sorry
