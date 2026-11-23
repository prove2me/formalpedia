-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_normAt_eq_norm
-- name    : Formalism.IndefR.LatticeTransfer.BlockMetrics.normAt_eq_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:58.557545+00:00
-- url     : https://prove2.me/theorems/de69a1cb-6a6c-404c-85b0-9d9bb3dd64e5
-- title:
--   Block Metrics: norm At eq norm
-- statement:
--   The Block Metrics construction uses the norm At eq norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean#L89-L93

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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)

theorem Formalism.IndefR.LatticeTransfer.BlockMetrics.normAt_eq_norm (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x =
      ‖(WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι)‖ := by sorry
