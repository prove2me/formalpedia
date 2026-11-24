-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_sum_normSq_pos
-- name    : Formalism.L2.Pj.DatLin.sum_normSq_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:05.186984+00:00
-- url     : https://prove2.me/theorems/a59cbcb0-0973-45f2-a5d9-1be52e956301
-- title:
--   Dat Lin: sum norm Sq pos
-- statement:
--   The Dat Lin construction uses the sum norm Sq pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L20-L22

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
variable {m : Type} [Fintype m] [DecidableEq m]

theorem Formalism.L2.Pj.DatLin.sum_normSq_pos {w : m → ℂ} (hw : w ≠ 0) : 0 < ∑ i, Complex.normSq (w i) := by sorry
