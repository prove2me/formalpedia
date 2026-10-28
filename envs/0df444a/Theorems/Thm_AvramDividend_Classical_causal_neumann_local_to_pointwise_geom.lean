-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_local_to_pointwise_geom
-- name    : AvramDividend.Classical.causal_neumann_local_to_pointwise_geom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:17:28.324773+00:00
-- url     : https://prove2.me/theorems/db188486-3ce1-427c-a71a-26d53d652d87
-- title:
--   Local geometric Gaussian Neumann bounds extend to every time
-- statement:
--   For Gaussian Neumann corrections with constant zeroth term and zero noninitial corrections on the nonpositive half-line, geometric bounds on all positive causal intervals imply geometric summability at every real point.
-- source:
--   Positive x belongs to Ioc(0,x) and inherits the proved local uniform geometric estimate. At x≤0 all n≥1 corrections vanish and Q0=1/a, so the fixed nonnegative constant 1/a is a pointwise geometric majorant. This closes the pointwise bound hypothesis of causal_geometric_neumann_resolvent.

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical Set

theorem AvramDividend.Classical.causal_neumann_local_to_pointwise_geom
    (Q : ℕ → ℝ → ℝ) (a ρ : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ)
    (hQ0 : Q 0 = fun _ : ℝ => 1 / a)
    (hzero : ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → Q (n + 1) x = 0)
    (hLocal : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ s ∈ Ioc (0 : ℝ) x,
        ‖Q n s‖ ≤ C * ρ ^ n) :
    ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ‖Q n x‖ ≤ C * ρ ^ n := by sorry
