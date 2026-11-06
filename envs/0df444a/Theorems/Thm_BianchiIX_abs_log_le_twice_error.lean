-- Prove2me | Theorems.Thm_BianchiIX_abs_log_le_twice_error
-- name    : BianchiIX.abs_log_le_twice_error
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T04:21:31.795541+00:00
-- url     : https://prove2.me/theorems/9f962329-9bed-4d79-bb63-b56c503dbafc
-- title:
--   A small relative error controls the logarithm
-- statement:
--   For real $t,e$, if $e\leq1/4$ and
--   $|t-1|\leq e$, then $|\log t|\leq2e$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/InverseLogDistortion.lean#L11-L22

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.abs_log_le_twice_error {t e : ℝ} (he : e ≤ 1 / 4) (ht : |t - 1| ≤ e) :
    |Real.log t| ≤ 2 * e := by sorry
