-- Prove2me | Theorems.Thm_AccelSGDGrowth_proposition_5_1
-- name    : AccelSGDGrowth.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:46.159724+00:00
-- url     : https://prove2.me/theorems/0363bc4e-5d3b-4050-b1c8-ac67e2a550f5
-- title:
--   Proposition 5.1 — the tail-averaged recursion bounds (5.7), (5.9)–(5.11) (corrected: no final $O(\gamma_3\log k/k)$, false at $\gamma_3=0$)
-- statement:
--   Consider nonnegative sequences $(e_t),(s_t)$ and the recursion (5.2), $e_{t+1}\le(1-\gamma_1r_t)e_t-\gamma_2r_ts_t+\gamma_3r_t^2$.
--
--   1. **First phase, (5.7).** Let $0<\gamma_1\le\gamma_4$, $\gamma_2\ge0$, $\gamma_3\ge0$, $\alpha>0$, $1\le k_1\le k$ with $\alpha k<\gamma_4$, and let (5.2) hold with $r_t=1/\gamma_4$ for $k_1\le t\le k$. Then
--   $$
--   \frac{\gamma_2}{\gamma_4}s_k\le\Big(1-\frac{\gamma_1}{\gamma_4}\Big)^{k-k_1+1}e_{k_1}+\frac{\gamma_3}{\gamma_1\gamma_4},\qquad \frac{\gamma_2}{\gamma_4}s_k\le e_{k_1}\exp\Big[-\frac{\gamma_1(k-k_1+1)}{\gamma_4}\Big]+\frac{\gamma_3}{\gamma_1\alpha k}.
--   $$
--   With $k_1=1$ this is (5.7).
--   2. **Second phase, (5.8)–(5.9).** Let $\gamma_1>0$, $\gamma_2\ge0$, $\gamma_3\ge0$, $1\le K\le k$, and let (5.2) hold with $r_t=1/(\gamma_1t)$ for $K\le t\le k$. Then
--   $$
--   \gamma_2\sum_{t=K}^k s_t\le\gamma_1(K-1)e_K+\frac{\gamma_3}{\gamma_1}(\log k+1).
--   $$
--   3. **The schedule (5.4).** Let $0<\gamma_1\le\gamma_4$, $\gamma_2\ge0$, $\gamma_3\ge0$, $\alpha>0$, let (5.2) hold for all $t\ge1$ with $r_t$ from (5.4), and put $k_0=\lceil\gamma_4/\alpha\rceil$. For every $k\ge k_0$: $W_k=k-k_0+1$;
--   $$
--   \gamma_2\sum_{t=1}^kw_{k,t}s_t\le\frac{\gamma_1\gamma_4e_{k_0}}{\alpha}+\frac{\gamma_3(\log k+1)}{\gamma_1}\ \ (5.9),\qquad e_{k_0}\le e_1\exp\Big[-\frac{\gamma_1(k_0-1)}{\gamma_4}\Big]+\frac{\gamma_3}{\gamma_1\gamma_4}\ \ (5.10),
--   $$
--   $$
--   \frac{\gamma_2}{W_k}\sum_{t=1}^kw_{k,t}s_t\le\frac{\gamma_1\gamma_4}{(k-k_0+1)\alpha}\Big\{e_1\exp\Big[-\frac{\gamma_1(k_0-1)}{\gamma_4}\Big]+\frac{\gamma_3}{\gamma_1\gamma_4}\Big\}+\frac{\gamma_3(\log k+1)}{(k-k_0+1)\gamma_1}\ \ (5.11).
--   $$
--
--   Together these give the two-phase bound behind (5.5): exponential decay in the first phase, and a $1/k$ bias tail plus a $\gamma_3\log k/k$ variance term in the second.
--
--   Differences from the source:
--   - correction: (5.5): (1/W_k)Σ w_{k,t}s_t = O(exp[−γ₁k/γ₄] + γ₃ log k/k) for all k ≥ 1, and the final '= O(γ₃ log k/k)' of (5.11) → the explicit bounds (5.7), (5.9), (5.10), (5.11) without the O; reason: false at γ₃ = 0: with γ₁ = 1/2, γ₂ = γ₄ = 1, γ₃ = 0, α = 0.6 (k₀ = 2), e_1 = 2, s_1 = 1/10, e_2 = 9/10, and for t ≥ 2 s_t = e_t/4, e_{t+1} = (1 − 3/(2t))e_t, (5.2) holds with r_t ≤ 1/γ₄, yet the left side of (5.5) is at least s_2/(k − 1) = 9/(40(k − 1)), not O(exp(−k/2))
--   - generalization: γ₄/α an integer (p.22, 'for simplifying our presentation') → any α > 0, with k₀ = ⌈γ₄/α⌉, the first k with αk ≥ γ₄; reason: for integer γ₄/α, k₀ = γ₄/α and every formula specializes to the printed one
--   - generalization: (5.2) with the conditions r_k ≤ 1/γ₄ and γ₁/γ₄ ≤ 1 → γ₁ ≤ γ₄ kept; r_k ≤ 1/γ₄ not assumed in clauses 2 and 3; reason: their proofs do not use it; with r_k ≤ 1/γ₄ added they are the page's statements
--   - generalization: positive sequences {e_k, s_k, r_k} → nonnegative e and s; reason: positive sequences are nonnegative
--   - generalization: (5.7) for the recursion started at t = 1; (5.9) started at t = γ₄/α → clause 1 with any start index k₁ ≥ 1; clause 2 with any start index K ≥ 1; reason: k₁ = 1 and K = γ₄/α give the printed displays; DAM+'s recursion starts at k = 2
--   - encoding: (5.9) as Σ_{t=1}^k w_{k,t}s_t with w_{k,t} = 0 for t < γ₄/α → clause 2 as Σ_{t=K}^k s_t; reason: the same sum, written without the zero weights
--   - encoding: non-negative constants γ₁, γ₂, γ₃ → 0 < γ₁, 0 ≤ γ₂, 0 ≤ γ₃; reason: r_t = 1/(γ₁t) in (5.4) and γ₃/(γ₁γ₄) are undefined at γ₁ = 0, so γ₁ = 0 is not an instance of the page
--   - encoding: (5.7) with left side (γ₂/(W_kγ₄))Σ_{t=1}^k w_{k,t}s_t for αk < γ₄ → clause 1 with left side (γ₂/γ₄)s_k; reason: the page's own first equality: for αk < γ₄, (5.4) gives W_k = 1 and Σ_t w_{k,t}s_t = s_k
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, Proposition 5.1, (5.5)–(5.11), pp.22–23, with (5.2) and (5.4), p.22

import Definitions.Def_AccelSGDGrowth_scheduleR
import Definitions.Def_AccelSGDGrowth_totalWeight

namespace AccelSGDGrowth

/-- Chen, Na, Kolar, arXiv:2006.06782v4, Proposition 5.1, p.23, stated through its displays (5.7),
(5.9), (5.10) and (5.11) (corrected: the final `O(·)` of (5.5) is not asserted). The recursion (5.2),
p.22, is `e_{t+1} ≤ (1 − γ₁r_t)e_t − γ₂r_t s_t + γ₃r_t²` for nonnegative sequences `e`, `s`.

1. **First phase, (5.7).** Let `0 < γ₁ ≤ γ₄`, `γ₂ ≥ 0`, `γ₃ ≥ 0`, `α > 0`, `1 ≤ k₁ ≤ k` with
   `αk < γ₄`, and let (5.2) hold with `r_t = 1/γ₄` for `k₁ ≤ t ≤ k`. Then
   `(γ₂/γ₄)s_k ≤ (1 − γ₁/γ₄)^{k−k₁+1} e_{k₁} + γ₃/(γ₁γ₄)` and
   `(γ₂/γ₄)s_k ≤ e_{k₁} exp[−γ₁(k−k₁+1)/γ₄] + γ₃/(γ₁αk)`. With `k₁ = 1` this is (5.7).
2. **Second phase, (5.8)–(5.9).** Let `γ₁ > 0`, `γ₂ ≥ 0`, `γ₃ ≥ 0`, `1 ≤ K ≤ k`, and let (5.2) hold with
   `r_t = 1/(γ₁t)` for `K ≤ t ≤ k`. Then `γ₂ Σ_{t=K}^k s_t ≤ γ₁(K − 1)e_K + (γ₃/γ₁)(log k + 1)`.
3. **The schedule (5.4), (5.9)–(5.11).** Let `0 < γ₁ ≤ γ₄`, `γ₂ ≥ 0`, `γ₃ ≥ 0`, `α > 0`, and let (5.2)
   hold for all `t ≥ 1` with `r_t` of (5.4). Put `k₀ = ⌈γ₄/α⌉`. Then for every `k ≥ k₀`:
   `W_k = k − k₀ + 1`; (5.9) `γ₂ Σ_{t=1}^k w_{k,t}s_t ≤ γ₁γ₄e_{k₀}/α + γ₃(log k + 1)/γ₁`;
   (5.10) `e_{k₀} ≤ e_1 exp[−γ₁(k₀ − 1)/γ₄] + γ₃/(γ₁γ₄)`; and (5.11)
   `(γ₂/W_k) Σ_{t=1}^k w_{k,t}s_t ≤ γ₁γ₄/((k − k₀ + 1)α) {e_1 exp[−γ₁(k₀ − 1)/γ₄] + γ₃/(γ₁γ₄)}
   + γ₃(log k + 1)/((k − k₀ + 1)γ₁)`.

**Formalization Note.** The page assumes `γ₄/α` is an integer; here `k₀ = ⌈γ₄/α⌉`, the first `k`
with `αk ≥ γ₄`, which equals `γ₄/α` when that is an integer. The condition `r_k ≤ 1/γ₄` attached to
(5.2) is not assumed in clauses 2 and 3 (their proofs do not use it, and DAM+ with `α > γ₁` violates
it). Positive sequences are relaxed to nonnegative ones. The page's nonnegative `γ₁` is taken
positive: `r_t = 1/(γ₁t)` in (5.4) and `γ₃/(γ₁γ₄)` are undefined at `γ₁ = 0`.
The `O(γ₃ log k/k)` of (5.11) and the `O` of
(5.5) are dropped: for `γ₃ = 0` they are false (the bias term decays only like `1/k`). -/
theorem proposition_5_1 :
    (∀ (γ₁ γ₂ γ₃ γ₄ α : ℝ) (e s : ℕ → ℝ) (k₁ k : ℕ),
      0 < γ₁ → γ₁ ≤ γ₄ → 0 ≤ γ₂ → 0 ≤ γ₃ → 0 < α → 1 ≤ k₁ → k₁ ≤ k → α * (k : ℝ) < γ₄ →
      (∀ t : ℕ, k₁ ≤ t → t ≤ k + 1 → 0 ≤ e t) → (∀ t : ℕ, k₁ ≤ t → t ≤ k → 0 ≤ s t) →
      (∀ t : ℕ, k₁ ≤ t → t ≤ k →
        e (t + 1) ≤ (1 - γ₁ * (1 / γ₄)) * e t - γ₂ * (1 / γ₄) * s t + γ₃ * (1 / γ₄) ^ 2) →
      γ₂ / γ₄ * s k ≤ (1 - γ₁ / γ₄) ^ (k - k₁ + 1) * e k₁ + γ₃ / (γ₁ * γ₄) ∧
      γ₂ / γ₄ * s k ≤
        e k₁ * Real.exp (-(γ₁ * ((k - k₁ + 1 : ℕ) : ℝ) / γ₄)) + γ₃ / (γ₁ * α * (k : ℝ))) ∧
    (∀ (γ₁ γ₂ γ₃ : ℝ) (e s : ℕ → ℝ) (K k : ℕ),
      0 < γ₁ → 0 ≤ γ₂ → 0 ≤ γ₃ → 1 ≤ K → K ≤ k →
      (∀ t : ℕ, K ≤ t → t ≤ k + 1 → 0 ≤ e t) → (∀ t : ℕ, K ≤ t → t ≤ k → 0 ≤ s t) →
      (∀ t : ℕ, K ≤ t → t ≤ k →
        e (t + 1) ≤ (1 - γ₁ * (1 / (γ₁ * t))) * e t - γ₂ * (1 / (γ₁ * t)) * s t +
          γ₃ * (1 / (γ₁ * t)) ^ 2) →
      γ₂ * ∑ t ∈ Finset.Icc K k, s t ≤
        γ₁ * ((K : ℝ) - 1) * e K + γ₃ / γ₁ * (Real.log k + 1)) ∧
    (∀ (γ₁ γ₂ γ₃ γ₄ α : ℝ) (e s : ℕ → ℝ),
      0 < γ₁ → γ₁ ≤ γ₄ → 0 ≤ γ₂ → 0 ≤ γ₃ → 0 < α →
      (∀ t : ℕ, 1 ≤ t → 0 ≤ e t) → (∀ t : ℕ, 1 ≤ t → 0 ≤ s t) →
      (∀ t : ℕ, 1 ≤ t →
        e (t + 1) ≤ (1 - γ₁ * scheduleR γ₁ γ₄ α t) * e t - γ₂ * scheduleR γ₁ γ₄ α t * s t +
          γ₃ * scheduleR γ₁ γ₄ α t ^ 2) →
      ∀ k : ℕ, ⌈γ₄ / α⌉₊ ≤ k →
        totalWeight γ₄ α k = (k : ℝ) - (⌈γ₄ / α⌉₊ : ℝ) + 1 ∧
        γ₂ * ∑ t ∈ Finset.Icc 1 k, scheduleW γ₄ α k t * s t ≤
          γ₁ * γ₄ * e ⌈γ₄ / α⌉₊ / α + γ₃ * (Real.log k + 1) / γ₁ ∧
        e ⌈γ₄ / α⌉₊ ≤
          e 1 * Real.exp (-(γ₁ * ((⌈γ₄ / α⌉₊ : ℝ) - 1) / γ₄)) + γ₃ / (γ₁ * γ₄) ∧
        γ₂ / totalWeight γ₄ α k * ∑ t ∈ Finset.Icc 1 k, scheduleW γ₄ α k t * s t ≤
          γ₁ * γ₄ / (((k : ℝ) - (⌈γ₄ / α⌉₊ : ℝ) + 1) * α) *
              (e 1 * Real.exp (-(γ₁ * ((⌈γ₄ / α⌉₊ : ℝ) - 1) / γ₄)) + γ₃ / (γ₁ * γ₄)) +
            γ₃ * (Real.log k + 1) / (((k : ℝ) - (⌈γ₄ / α⌉₊ : ℝ) + 1) * γ₁)) := by sorry

end AccelSGDGrowth
