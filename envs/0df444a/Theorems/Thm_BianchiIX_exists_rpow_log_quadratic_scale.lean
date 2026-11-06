-- Prove2me | Theorems.Thm_BianchiIX_exists_rpow_log_quadratic_scale
-- name    : BianchiIX.exists_rpow_log_quadratic_scale
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T07:02:57.351237+00:00
-- url     : https://prove2.me/theorems/7ebfa3ab-1233-4555-ab8e-d69930235191
-- title:
--   Every higher wall power absorbs a logarithmic quadratic loss
-- statement:
--   For every real $p>2$ there exists $a_*>0$ such that
--   $$0<a\leq a_*\quad\Longrightarrow\quad
--   a\leq1,\quad a^p\leq a^2,\quad a^p(1+|\log a|)\leq a^2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ShearTailEndpointScale.lean#L10-L40

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_rpow_log_quadratic_scale {p : ℝ} (hp : 2 < p) :
    ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
      a ≤ 1 ∧ a ^ p ≤ a ^ 2 ∧ a ^ p * (1 + |Real.log a|) ≤ a ^ 2 := by sorry
