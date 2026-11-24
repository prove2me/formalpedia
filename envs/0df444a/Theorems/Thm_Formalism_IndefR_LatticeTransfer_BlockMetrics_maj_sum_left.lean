-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_maj_sum_left
-- name    : Formalism.IndefR.LatticeTransfer.BlockMetrics.maj_sum_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:47.170788+00:00
-- url     : https://prove2.me/theorems/88149881-3518-45e7-9c18-fd8850ee8ecc
-- title:
--   Block Metrics: maj sum left
-- statement:
--   The Block Metrics construction uses the maj sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean#L34-L41

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

theorem Formalism.IndefR.LatticeTransfer.BlockMetrics.maj_sum_left {α : Type} (s : Finset α) (c : α → K) (f : α → V) (y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (∑ a ∈ s, c a • f a) y =
      ∑ a ∈ s, star (v.embedding (c a)) * Formalism.HermitianLatticesTheory.majAt b X v (f a) y := by sorry
