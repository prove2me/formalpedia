-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_fcoord_map
-- name    : Formalism.IndefR.LatticeTransfer.BlockMetrics.fcoord_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:58.825542+00:00
-- url     : https://prove2.me/theorems/acdde044-fb54-47b9-8a17-4e15a78ad8b0
-- title:
--   Block Metrics: fcoord map
-- statement:
--   The Block Metrics construction uses the fcoord map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean#L95-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean#L95-L106

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

theorem Formalism.IndefR.LatticeTransfer.BlockMetrics.fcoord_map (hX : ∀ v, IsUnit (X v).det) (φ : V →ₗ[K] V) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (φ x) =
      ((X v)⁻¹ * (LinearMap.toMatrix b b φ).map v.embedding * X v).mulVec
        (Formalism.HermitianLatticesTheory.fcoord b X v x) := by sorry
