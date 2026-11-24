-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_opNormAt_le_of_points
-- name    : Formalism.IndefR.LatticeTransfer.BlockMetrics.opNormAt_le_of_points
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:13:13.331024+00:00
-- url     : https://prove2.me/theorems/b0f92f15-628d-4634-b1b7-4fd834fc4289
-- title:
--   Block Metrics: op Norm At le of points
-- statement:
--   The Block Metrics construction uses the op Norm At le of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean#L159-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean#L159-L177

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

theorem Formalism.IndefR.LatticeTransfer.BlockMetrics.opNormAt_le_of_points {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (φ : V →ₗ[K] V) (v : InfinitePlace K) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f, Formalism.HermitianLatticesTheory.normAt b X v (φ f) ≤ C * Formalism.HermitianLatticesTheory.normAt b X v f) :
    Formalism.HN.opNormAt b X b X v φ ≤ C := by sorry
