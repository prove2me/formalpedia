-- Prove2me | Theorems.Thm_BianchiIX_exists_common_rpow_budget
-- name    : BianchiIX.exists_common_rpow_budget
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T20:05:11.88084+00:00
-- url     : https://prove2.me/theorems/b627d301-18c4-4af6-8129-acc43a5e38a2
-- title:
--   A common small-amplitude threshold for finitely many errors
-- statement:
--   Let $s$ be a finite set, and let $C_i\geq0$, $p_i>0$,
--   $\varepsilon_i>0$ for $i\in s$. For every $U>0$, there exists
--   $0<B_{\max}<U$ such that
--   $$C_iB^{p_i}<\varepsilon_i
--   \quad(0<B\leq B_{\max},\ i\in s).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/SmallParameters.lean#L43-L63

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_common_rpow_budget {ι : Type*} (s : Finset ι) {C p ε : ι → ℝ} {upper : ℝ}
    (hC : ∀ i ∈ s, 0 ≤ C i) (hp : ∀ i ∈ s, 0 < p i)
    (hε : ∀ i ∈ s, 0 < ε i) (hu : 0 < upper) :
    ∃ Bmax : ℝ, 0 < Bmax ∧ Bmax < upper ∧
      ∀ B ∈ Ioc 0 Bmax, ∀ i ∈ s, C i * B ^ p i < ε i := by sorry
