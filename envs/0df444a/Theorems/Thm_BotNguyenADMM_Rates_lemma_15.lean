-- Prove2me | Theorems.Thm_BotNguyenADMM_Rates_lemma_15
-- name    : BotNguyenADMM.Rates.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:07:26.03477+00:00
-- url     : https://prove2.me/theorems/05169f61-2af5-4f24-8e72-d2c6cf0bf3e6
-- title:
--   Lemma 15 — rates for decreasing sequences with $e_{k-l_0} - e_k \ge C_e e_k^{2\theta}$
-- statement:
--   Let $(e_k)_{k\ge0}$ be a monotonically decreasing sequence of nonnegative reals converging to $0$, and let $k_0\ge l_0\ge1$ be natural numbers such that
--   $$e_{k-l_0} - e_k \ge C_e\, e_k^{2\theta}\qquad\text{for every } k\ge k_0, \qquad (71)$$
--   where $C_e>0$ and $\theta\in[0,1)$. Then:
--   1. if $\theta = 0$, the sequence converges in finite time: $e_k = 0$ for all large $k$;
--   2. if $\theta\in(0,\frac12]$, there are $C_{e,0}>0$ and $Q\in[0,1)$ with $0\le e_k\le C_{e,0}Q^k$ for every $k\ge k_0$;
--   3. if $\theta\in(\frac12,1)$, there is $C_{e,1}>0$ with
--   $$0\le e_k\le C_{e,1}(k - l_0 + 1)^{-\frac{1}{2\theta-1}}\qquad\text{for every } k\ge k_0 + l_0.$$
--
--   This purely real lemma turns the recurrence inequality of Lemma 17 into the finite, linear and sublinear rates of Theorem 18.
--
--   **Formalization Note** In (71) the power $e_k^{2\theta}$ is read with the convention $0^{0}=0$ (written `if e k = 0 then 0 else e k ^ (2θ)`): with Lean's $0^0 = 1$, (71) at $\theta=0$ would be unsatisfiable by any sequence tending to $0$ and part 1 would be vacuous. For $\theta>0$ the convention changes nothing. The constants are quantified after $e$, $k_0$, $l_0$, $C_e$ and $\theta$.
-- source:
--   Boţ and Nguyen, The proximal ADMM in the nonconvex setting, arXiv:1801.01994v2, p. 23, Lemma 15, (71)

import Mathlib

namespace BotNguyenADMM.Rates

/-- **Lemma 15** (Boţ–Nguyen, arXiv:1801.01994v2, p. 23). Let `(e_k)_{k≥0}` be nonnegative,
monotonically decreasing and convergent to `0`, and let `k₀ ≥ l₀ ≥ 1` be such that
`e_{k−l₀} − e_k ≥ C_e e_k^{2θ}` for every `k ≥ k₀` (71), with `C_e > 0`, `θ ∈ [0, 1)`, and the
convention `0^{2θ} = 0`. Then (i) `θ = 0`: `e` is eventually `0`; (ii) `θ ∈ (0, 1/2]`:
`0 ≤ e_k ≤ C_{e,0} Q^k` for `k ≥ k₀`; (iii) `θ ∈ (1/2, 1)`:
`0 ≤ e_k ≤ C_{e,1}(k − l₀ + 1)^{−1/(2θ−1)}` for `k ≥ k₀ + l₀`. -/
theorem lemma_15 (e : ℕ → ℝ) (he_nonneg : ∀ k, 0 ≤ e k) (he_anti : Antitone e)
    (he_lim : Filter.Tendsto e Filter.atTop (nhds 0)) (k₀ l₀ : ℕ) (hl₀ : 1 ≤ l₀) (hkl : l₀ ≤ k₀)
    (Ce θ : ℝ) (hCe : 0 < Ce) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h71 : ∀ k ≥ k₀, Ce * (if e k = 0 then 0 else e k ^ (2 * θ)) ≤ e (k - l₀) - e k) :
    (θ = 0 → ∃ K : ℕ, ∀ k ≥ K, e k = 0) ∧
    (0 < θ ∧ θ ≤ 1 / 2 → ∃ Ce0 : ℝ, 0 < Ce0 ∧ ∃ Q : ℝ, 0 ≤ Q ∧ Q < 1 ∧
      ∀ k ≥ k₀, 0 ≤ e k ∧ e k ≤ Ce0 * Q ^ k) ∧
    (1 / 2 < θ ∧ θ < 1 → ∃ Ce1 : ℝ, 0 < Ce1 ∧
      ∀ k ≥ k₀ + l₀, 0 ≤ e k ∧ e k ≤ Ce1 * ((k : ℝ) - l₀ + 1) ^ (-(1 / (2 * θ - 1)))) := by sorry

end BotNguyenADMM.Rates
