-- Prove2me | Theorems.Thm_AlgoPFR_claim_4_13_good_trajectory
-- name    : AlgoPFR.claim_4_13_good_trajectory
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:32.915199+00:00
-- url     : https://prove2.me/theorems/015e6084-7e44-417a-b7b7-bfb3620da2e1
-- title:
--   Claim 4.13 — a good trajectory of $T=O(\log\log K)$ iterations has probability $\Omega(1/\mathrm{polylog}\,K)$
-- statement:
--   Let $\eta\in(0,1)$ have the property of Theorem 4.3. There are constants $c>0$, $c'$ and $C$ such that for every nonempty $A\subseteq\mathbb F_2^n$ with $|A+A|\le K|A|$ the following holds for $T=\min\{t\ge0:(1-\eta/2)^t\log K\le d_{\mathrm{term}}\}$ iterations of Algorithm 2 from $X_0=Y_0=U_A$.
--
--   1. With probability at least $c/(\log 2K)^{c'}$, every iteration is good in the sense of Claim 4.12.
--   2. On every such trajectory, $d[X_T;Y_T]\le d_{\mathrm{term}}$, $\Delta[X_T],\Delta[Y_T]\le L_0$, and
--   $$\sum_{t<T}(\tilde d_t+1)\le C(\log K+2),\qquad d[U_A;X_T]\le C(\log K+2),$$
--   where $\tilde d_t=\max\{d[X_t;Y_t],d_{\mathrm{term}}\}$.
--   3. $T\le C(\log\log K+2)$ when $\log K>d_{\mathrm{term}}$, and $T=0$ otherwise.
--
--   This is what repetition amplifies: one trajectory is good only with polylogarithmically small probability, but it reaches a pair of constant distance and slack, at distance $O(\log K)$ from $U_A$.
--
--   Differences from the source:
--
--   - generalization: K ∈ ℕ (context of Theorem 4.2) → real K, with |A + A| ≤ K|A|; reason: natural K are a special case; only log K enters the proof
--   - generalization: η the constant fixed after Theorem 4.3 → every η ∈ (0, 1) with IsDecrementConstant η; reason: the fixed constant is one such η, once taken below 1
--   - reading: Algorithm 2, with its budget checks on lines 9–11 → the trajectory law without the budget checks; reason: the claim counts iterations and goodness; budgets enter only in Claim 4.15
--   - encoding: Ω(1 / polylog K), O(log K), T = O(log log K) → c / (log 2K)^c′, C(log K + 2), and T ≤ C(log log K + 2) for log K > d_term with T = 0 otherwise; reason: the shorthands of p.13 and Eq. (61)
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Claim 4.13, p.35

import Mathlib
import Definitions.Def_AlgoPFR_Iteration

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Claim 4.13.** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.35: running Algorithm 2 for `T = O(log log K)` iterations (Eq. (57)) from
`X₀ = Y₀ = U_A`, with probability `Ω(1/polylog K)` each iteration is good in the sense of Claim 4.12,
and then `d_T ≤ d_term`, `Δ[X_T], Δ[Y_T] ≤ L₀`, `∑_{t<T} (d̃_t + 1) = O(log K)` and
`d[U_A;X_T] = O(log K)`, with `d̃_t := max {d[X_t;Y_t], d_term}`.

**Formalization Note.** Per p.13, `polylog K` is `(log (2K))^{O(1)}` and `O(log K)` is `O(log K + 2)`. The
constants are chosen after `η` and before `n, A, K`. The trajectory is the iterated random kernel,
without the budget checks of Algorithm 2 (Claim 4.13 counts iterations; the budgets enter through
Claim 4.15). `T = O(log log K)` is the paper's Eq. (61), for `log K > d_term`; otherwise `T = 0`. `K` is
real; the hypothesis forces `K ≥ 1`. -/
theorem claim_4_13_good_trajectory (η : ℝ) (h0 : 0 < η) (h1 : η < 1)
    (hη : IsDecrementConstant η) :
    ∃ (c C : ℝ) (c' : ℕ), 0 < c ∧ ∀ (n : ℕ) (A : Finset (Vec n)) (hA : A.Nonempty) (K : ℝ),
      ((A + A).card : ℝ) ≤ K * A.card →
      ENNReal.ofReal (c / Real.logb 2 (2 * K) ^ c') ≤
          (trajectoryLaw (iterationBound η K) (rootState A hA)).toOuterMeasure
            {τ | ∀ e ∈ τ, IsGoodIteration η e.1 e.2} ∧
        (∀ τ ∈ (trajectoryLaw (iterationBound η K) (rootState A hA)).support,
          (∀ e ∈ τ, IsGoodIteration η e.1 e.2) →
            (finalState (rootState A hA) τ).dist ≤ dTerm η ∧
            slack (finalState (rootState A hA) τ).X (finalState (rootState A hA) τ).MX ≤ L0 η ∧
            slack (finalState (rootState A hA) τ).Y (finalState (rootState A hA) τ).MY ≤ L0 η ∧
            (τ.map fun e => e.1.dTilde η + 1).sum ≤ C * (Real.logb 2 K + 2) ∧
            rd (uniformLaw A hA) (finalState (rootState A hA) τ).X.sample ≤
              C * (Real.logb 2 K + 2)) ∧
        (dTerm η < Real.logb 2 K →
          (iterationBound η K : ℝ) ≤ C * (Real.logb 2 (Real.logb 2 K) + 2)) ∧
        (Real.logb 2 K ≤ dTerm η → iterationBound η K = 0) := by sorry

end AlgoPFR
