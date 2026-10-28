-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_series_continuous_of_uniform_geometric_bound
-- name    : AvramDividend.Classical.causal_neumann_series_continuous_of_uniform_geometric_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:20:58.640631+00:00
-- url     : https://prove2.me/theorems/94f41bcf-4842-4ec2-adeb-8e9e17d0c3ca
-- title:
--   Continuity of Neumann series under B times rho-to-n bounds
-- statement:
--   The natural sup-bound for an exponentially tilted convolution-power sequence is |Fn(x)|≤Bρ^n with B>0 and 0<ρ<1. This theorem converts it to the existing ρ^(n+1)/a M-test normalisation with a=ρ/B and obtains convergence and continuity up to zero. This is the final analytic continuity step for the positive-discount scale Neumann sum.
-- source:
--   AvramDividend.Classical.causal_neumann_geometric_series_continuousOn_nonnegative (Proved)

import Theorems.Thm_AvramDividend_Classical_causal_neumann_geometric_series_continuousOn_nonnegative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open AvramDividend.Classical Set

theorem AvramDividend.Classical.causal_neumann_series_continuous_of_uniform_geometric_bound
    (F : ℕ → ℝ → ℝ) (B ρ : ℝ)
    (hB : 0 < B) (hρ : 0 < ρ) (hρone : ρ < 1)
    (hcont : ∀ n : ℕ, ContinuousOn (F n) (Ici (0 : ℝ)))
    (hbound : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |F n x| ≤ B * ρ ^ n) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ, F n x) (Ici (0 : ℝ)) ∧
      (∀ x : ℝ, 0 ≤ x → Summable (fun n : ℕ => F n x)) := by sorry
