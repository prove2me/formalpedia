-- Prove2me | Theorems.Thm_BlindProphetSec_Blind_lemma_4_2
-- name    : BlindProphetSec.Blind.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:00.997831+00:00
-- url     : https://prove2.me/theorems/cf73205b-f9bb-46ae-ac5b-e7ab8d2572a4
-- title:
--   Lemma 4.2, p. 12 — Σᵢ P(Vᵢ > t)/(1 − (1/n) Σ_{l∈[k]} P(Vᵢ > τ_l)) ≥ P(max > t)/(1 − (k/n) P(max > τ₁)) for t < τ₁, k ≤ n/2
-- statement:
--   Let $V_1,\dots,V_n$ ($n\ge1$) be independent random variables and let $\tau_1,\dots,\tau_n$ be thresholds with $\tau_1\ge\max\{\tau_2,\dots,\tau_n\}$. Then for every $t<\tau_1$ and every integer $k$ with $0\le k\le n/2$,
--   $$\sum_{i\in[n]}\frac{\mathbb P(V_i>t)}{1-\frac1n\sum_{l\in[k]}\mathbb P(V_i>\tau_l)}\;\ge\;\frac{\mathbb P(\max_{i\in[n]}V_i>t)}{1-\frac kn\,\mathbb P(\max_{i\in[n]}V_i>\tau_1)}.$$
--
--   The lemma replaces the union bound $\sum_i\mathbb P(V_i>t)\ge\mathbb P(\max_iV_i>t)$ used in Section 3 by a weighted version, which is what improves the constant from 0.665 to 0.669.
--
--   **Formalization Note.** The thresholds need not be monotone beyond $\tau_1\ge\tau_l$. Both denominators are at least $1/2$ because $k\le n/2$, so the real divisions are genuine. The index $l\in[k]$ is the 0-based `l.val < k`; $\tau_1$ is `τ 0`. Continuity and nonnegativity are not assumed, as on the page.
-- source:
--   Correa, Saona & Ziliotto, Prophet Secretary Through Blind Strategies, arXiv:1807.07483v2, p. 12, Lemma 4.2; proof pp. 12–13

import Mathlib
import Definitions.Def_BlindProphetSec_Blind_Setting

namespace BlindProphetSec.Blind

open MeasureTheory

theorem lemma_4_2 {n : ℕ} [NeZero n] (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (τ : Fin n → ℝ) (hτ : ∀ l, τ l ≤ τ 0) (t : ℝ) (ht : t < τ 0) (k : ℕ) (hk : 2 * k ≤ n) :
    PmaxGT μ t / (1 - (k : ℝ) / n * PmaxGT μ (τ 0)) ≤
      ∑ i : Fin n, (μ i (Set.Ioi t)).toReal /
        (1 - (1 / (n : ℝ)) * ∑ l ∈ Finset.univ.filter (fun l : Fin n => l.val < k),
          (μ i (Set.Ioi (τ l))).toReal) := by sorry

end BlindProphetSec.Blind
