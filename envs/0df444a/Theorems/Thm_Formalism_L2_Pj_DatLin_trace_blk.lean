-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_trace_blk
-- name    : Formalism.L2.Pj.DatLin.trace_blk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:24.327831+00:00
-- url     : https://prove2.me/theorems/643ca405-eb8a-4dae-874f-2165a74d37f4
-- title:
--   Dat Lin: trace blk
-- statement:
--   The Dat Lin construction uses the trace blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L151-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L151-L153

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open Matrix Complex
variable {ι n : Type} [Fintype ι] [Fintype n]

theorem Formalism.L2.Pj.DatLin.trace_blk [DecidableEq ι] [DecidableEq n] (N : ι → Matrix n n ℂ) :
    LinearMap.trace ℝ _ (blk N) = ∑ τ, 2 * (N τ).trace.re := by sorry
