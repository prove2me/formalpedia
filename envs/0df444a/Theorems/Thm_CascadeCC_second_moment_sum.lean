-- Prove2me | Theorems.Thm_CascadeCC_second_moment_sum
-- name    : CascadeCC.second_moment_sum
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:49.430264+00:00
-- url     : https://prove2.me/theorems/447deaa2-3025-492f-8a3e-acc190144374
-- title:
--   p.ec11 — $\sum_t\mathbf E[(\delta^v_{tj})^2]=O(\log k)$
-- statement:
--   Under the law of the Cascade Correction policy, for every horizon $N\ge1$, inventory $Y$, stationary rates $a$, and product $j$,
--
--   $$
--   \sum_{t=1}^N\mathbf E\bigl[(\delta^v_{tj})^2\bigr]\ \le\ 1+\log N .
--   $$
--
--   The increments of $\delta^v$ are orthogonal martingale differences, so the weights $1/(N-s)$ sum to a harmonic number. This is the estimate behind the bound on $\tau$ and every quadratic term of the loss.
--
--   Differences from the source:
--   - encoding: prices in Ω_p as actions, rates in Ω_α = [0, u] or (0, u] → rates in [0, u] as actions, with 0 the turn-off price and revenue 0; reason: A1 makes prices and rates equivalent and §4.2 does the same; S(y) and S^D(y) contain rate 0, and [0, u] covers both forms of Ω_α
--   - generalization: A1 (α_j twice differentiable) and A2 → not assumed; the instance carries only p_j, strictly decreasing with p_j(u) = 0, and A3 with strict concavity, the derivatives and the bound |r″_j| ≤ w required on (0, u] only; reason: A1 and A2 concern the price parametrization, and for Ω_α = [0, u] the conditions of A3 on (0, u] are implied by those on [0, u]; every instance of A1–A3 is an instance here
--   - reading: σ_j = σ_{j−1}(1 − α_j)ζ_j on pp.10, 14, but σ_{j+1} = σ_j(1 − α_j)ζ_j on pp.20, 24, Figure 1 and (EC.19) → σ_j(a) = λ∏_{i<j}(1 − a_i)ζ_i; reason: the source disagrees with itself; the form of pp.20, 24 is the one its analysis uses and the printed one has an index slip
--   - generalization: O(log k) → the explicit bound 1 + log N for every N ≥ 1; reason: E[(∆_sj)²] ≤ 1/4 and orthogonality give at most H_{N−1}/4 ≤ 1 + log N, and a bound in log N is one in log k since N = kT; it is a particular O(log k) bound
--   - generalization: the sum over t = 2, …, k − 1, with T = 1 → the sum over t = 1, …, N, for every a and Y; reason: the printed range is contained in this one, and all terms are nonnegative; the proof uses only rates in [0, u]
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, p.ec11, in the proof of Lemma EC.3

import Mathlib
import Definitions.Def_CascadeCC_Analysis

namespace CascadeCC

variable {J : ℕ}

/-- p.ec11, in the proof of Lemma EC.3 (SSRN abstract_id=3362921): the sum over the periods of
E[(δ^v_tj)²] is O(log k), in the explicit form ∑_{t ≤ N} E[(δ^v_tj)²] ≤ 1 + log N.

**Formalization Note** The expectation is under the law of the Cascade Correction policy. The range is
t = 1, …, N (t = s + 1), which contains the printed range 2, …, k − 1 of nonnegative terms. No hypothesis
on `a` or `Y` is needed, since the applied rates lie in [0, u]. -/
theorem second_moment_sum (M : Instance J) (a : Fin J → ℝ) (N : ℕ) (hN : 1 ≤ N) (Y : Fin J → ℕ)
    (j : Fin J) :
    ∑ s ∈ Finset.range N, ccExpect M N Y a (fun ω => (delta M N Y a ω s j) ^ 2) ≤
      1 + Real.log N := by sorry

end CascadeCC
