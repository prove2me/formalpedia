-- Prove2me | Theorems.Thm_BranchCascade_negative_seed_forces_next_index
-- name    : BranchCascade.negative_seed_forces_next_index
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:51:30.417826+00:00
-- url     : https://prove2.me/theorems/98410a10-11ac-4e89-a670-f9ea8234747e
-- title:
--   A stationary negative minimum forces the next negative index
-- statement:
--   Let n≥1 and a>0. Suppose Qₙ has an interior negative value smaller than both endpoint values on [a,b], is continuous there and differentiable inside, and satisfies Qₙ₊₁(u)=(2n-1)Qₙ(u)-uQₙ′(u) for u>0. Then some u>0 has Qₙ₊₁(u)<0.
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchCascade.negative_seed_forces_next_index     (Q : ℕ → ℝ → ℝ) (n : ℕ) (hn : 1 ≤ n) (a b x : ℝ)
    (ha0 : 0 < a) (hax : a < x) (hxb : x < b) (hx : Q n x < 0)
    (ha : Q n x < Q n a) (hb : Q n x < Q n b)
    (hc : ContinuousOn (Q n) (Icc a b))
    (hd : DifferentiableOn ℝ (Q n) (Ioo a b))
    (hrec : ∀ u > 0,
      Q (n+1) u = (2*(n:ℝ)-1)*Q n u - u*deriv (Q n) u) :
    ∃ u > 0, Q (n+1) u < 0 := by sorry
