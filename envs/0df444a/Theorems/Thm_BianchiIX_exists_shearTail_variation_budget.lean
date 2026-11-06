-- Prove2me | Theorems.Thm_BianchiIX_exists_shearTail_variation_budget
-- name    : BianchiIX.exists_shearTail_variation_budget
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:51:35.738902+00:00
-- url     : https://prove2.me/theorems/3e3a434c-9053-40e6-a53d-5a01761197d8
-- title:
--   A common small scale controls the shear tail variation moments
-- statement:
--   Let $C\geq0$, $q>2$, and $P>6D+2$. There exists $a_*>0$
--   such that every $0<a\leq a_*$ satisfies
--   $$a\leq1/256,\qquad2a^{P-6D-2}\leq1.$$
--   For all $L_0,J_0,J_1\in\mathbb R$ with
--   $$L_0\leq2+4Cq|\log a|,\quad0\leq J_0\leq4a,
--   \quad J_1\leq1/256+(2+D)a,$$
--   one has
--   $$9J_0\leq\log2,\quad2J_0+16J_1\leq1/2,
--   \quad L_0J_0\leq1/16.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ShearTailVariationBudget.lean#L11-L53

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

theorem BianchiIX.exists_shearTail_variation_budget {C q D P : ℝ}
    (hC : 0 ≤ C) (hq : 2 < q) (hP : 6 * D + 2 < P) :
    ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
      a ≤ 1 / 256 ∧ 2 * a ^ (P - 6 * D - 2) ≤ 1 ∧
      ∀ L₀ J₀ J₁ : ℝ, L₀ ≤ 2 + 4 * C * q * |Real.log a| → 0 ≤ J₀ →
        J₀ ≤ 4 * a → J₁ ≤ 1 / 256 + (2 + D) * a →
        9 * J₀ ≤ Real.log 2 ∧ 2 * J₀ + 16 * J₁ ≤ 1 / 2 ∧ L₀ * J₀ ≤ 1 / 16 := by sorry
