-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_exists_im_ne_zero
-- name    : Formalism.IndefR.LatticeTransfer.BlockMetrics.exists_im_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:45.258503+00:00
-- url     : https://prove2.me/theorems/0f609045-664c-41cb-b554-7443ac3374d1
-- title:
--   Block Metrics: exists im ne zero
-- statement:
--   The Block Metrics construction uses the exists im ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean#L207-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/OpNormAtLeOfPoints.lean#L207-L216

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

theorem Formalism.IndefR.LatticeTransfer.BlockMetrics.exists_im_ne_zero {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (v : InfinitePlace K) : ∃ a : K, (v.embedding a).im ≠ 0 := by sorry
