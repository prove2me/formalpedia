-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_fc_smul
-- name    : Formalism.IndefR.LatticeTransfer.BlockMetrics.fc_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:18.013945+00:00
-- url     : https://prove2.me/theorems/3af0575e-d744-4ec5-98a0-294de2ffcbae
-- title:
--   Block Metrics: fc smul
-- statement:
--   The Block Metrics construction uses the fc smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean#L20-L25

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

theorem Formalism.IndefR.LatticeTransfer.BlockMetrics.fc_smul (c : K) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.fcoord b X v x := by sorry
