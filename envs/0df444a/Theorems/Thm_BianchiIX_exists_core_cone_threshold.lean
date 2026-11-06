-- Prove2me | Theorems.Thm_BianchiIX_exists_core_cone_threshold
-- name    : BianchiIX.exists_core_cone_threshold
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T03:27:19.365197+00:00
-- url     : https://prove2.me/theorems/53879c4c-01d8-421f-bdfa-2bb64ead240a
-- title:
--   One wall threshold controls all three core cone errors
-- statement:
--   For $R,A,B\geq0$, there is
--   $0<\varepsilon\leq1/10000$ such that
--   $$7R\sqrt\varepsilon\leq1/32,\qquad
--   38400A\sqrt\varepsilon\leq1/32,\qquad
--   3B\sqrt\varepsilon\leq1/32.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/CoreCone.lean#L15-L33

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

theorem BianchiIX.exists_core_cone_threshold {R A B : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ ε > 0, ε ≤ 1 / 10000 ∧ 7 * R * Real.sqrt ε ≤ 1 / 32 ∧
      38400 * A * Real.sqrt ε ≤ 1 / 32 ∧ 3 * B * Real.sqrt ε ≤ 1 / 32 := by sorry
