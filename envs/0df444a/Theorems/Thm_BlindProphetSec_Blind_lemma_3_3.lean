-- Prove2me | Theorems.Thm_BlindProphetSec_Blind_lemma_3_3
-- name    : BlindProphetSec.Blind.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:39.021557+00:00
-- url     : https://prove2.me/theorems/7766af04-f603-49f6-9e51-4653acad1bdd
-- title:
--   Lemma 3.3, p. 8 — (1/n) Σ_{j≤k} (1 − αⱼ) ≤ P(T ≤ k) ≤ 1 − (Π_{j≤k} αⱼ)^{1/n}
-- statement:
--   Fix $\alpha_1,\dots,\alpha_n\in[0,1]$. Let $F_1,\dots,F_n$ be continuous laws of independent nonnegative random variables arriving in uniformly random order, and let $T$ be the stopping time of the threshold algorithm whose threshold $\tau_j$ at time $j$ satisfies $\mathbb P(\max_{i\in[n]}V_i\le\tau_j)=\alpha_j$. Then for every $k\in[n]$,
--   $$\frac1n\sum_{j\in[k]}(1-\alpha_j)\;\le\;\mathbb P(T\le k)\;\le\;1-\Big(\prod_{j=1}^k\alpha_j\Big)^{1/n}.$$
--
--   The lemma bounds the distribution of the stopping time by quantities that depend only on the levels $\alpha_j$, not on the instance; the lower bound is attained when only one variable is nonzero and the upper bound when all laws are equal.
--
--   **Formalization Note.** The threshold rule is encoded through the levels: the gambler stops at time $j$ iff $\alpha_j<\mathbb P(\max_iV_i\le V_{\sigma_j})$, which for continuous laws agrees almost surely with $V_{\sigma_j}>\tau_j$ for any $\tau_j$ with $\mathbb P(\max_iV_i\le\tau_j)=\alpha_j\in(0,1]$. Stating it with real thresholds $\tau_j$ as hypotheses would make the statement vacuous for $\alpha_j=1$ and unbounded laws (no real $\tau_j$ has $\mathbb P(\max\le\tau_j)=1$); the encoding reads $\alpha_j=1$ as "never stop". At $\alpha_j=0$ it uses the largest admissible threshold. No monotonicity of the $\alpha_j$ is assumed, as on the page. The $1/n$-th root is the real power $x^{1/n}$.
-- source:
--   Correa, Saona & Ziliotto, Prophet Secretary Through Blind Strategies, arXiv:1807.07483v2, p. 8, Lemma 3.3; proof pp. 9–10

import Mathlib
import Definitions.Def_BlindProphetSec_Blind_Setting

namespace BlindProphetSec.Blind

open MeasureTheory

theorem lemma_3_3 {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, NullSingletonClass (μ i)] (hnn : ∀ i, μ i (Set.Iio 0) = 0)
    (α : Fin n → ℝ) (hα : ∀ j, 0 ≤ α j ∧ α j ≤ 1) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (1 / (n : ℝ)) * ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), (1 - α j) ≤
        probVS μ (fun v σ => stopLE (levelAcc μ α v σ) k) ∧
      probVS μ (fun v σ => stopLE (levelAcc μ α v σ) k) ≤
        1 - (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), α j) ^ ((1 : ℝ) / n) := by sorry

end BlindProphetSec.Blind
