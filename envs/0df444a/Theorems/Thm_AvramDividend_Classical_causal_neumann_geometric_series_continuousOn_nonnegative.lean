-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_geometric_series_continuousOn_nonnegative
-- name    : AvramDividend.Classical.causal_neumann_geometric_series_continuousOn_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:49:13.681171+00:00
-- url     : https://prove2.me/theorems/cedc1744-a872-4149-bd49-9ce6713dd358
-- title:
--   Uniform geometric Neumann primitive convergence and boundary continuity
-- statement:
--   If each Neumann-primitive term is continuous on the nonnegative half-line and its magnitude is uniformly bounded by rho^(n+1)/a for a>0 and 0<=rho<1, then its sum is continuous up to zero and the defining series converges absolutely at every nonnegative point. Supplies two exact hypotheses for the Gaussian C1 derivative-resolvent assembly theorem.
-- source:
--   Classical Weierstrass bound using Mathlib continuousOn_tsum and summable_geometric_of_norm_lt_one.

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_neumann_series_C1_of_signed_power_bounds

open AvramDividend.Classical Set

theorem AvramDividend.Classical.causal_neumann_geometric_series_continuousOn_nonnegative
    (H : ℕ → ℝ → ℝ) (a ρ : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcont : ∀ n : ℕ, ContinuousOn (H n) (Ici (0 : ℝ)))
    (hbound : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ, H n x) (Ici (0 : ℝ)) ∧
      (∀ x : ℝ, 0 ≤ x → Summable (fun n : ℕ => H n x)) := by sorry
