-- Prove2me | Theorems.Thm_Erdos68_fixed_weight_minimum_and_range
-- name    : Erdos68.fixed_weight_minimum_and_range
-- status  : Proved
-- author  : @Mceppaglia
-- created : 2026-11-21T00:46:21.471975+00:00
-- url     : https://prove2.me/theorems/04d203bf-aae5-4674-bd37-508060e640c4
-- title:
--   Unique minimum and exact range of the Erdős 68 sum at a fixed factorial moment
-- statement:
--   For $j\ge 2$, set $w_j=1/(j!-1)$ and $x_j=1/j!$. Write $S=\sum_j w_j$, fix an integer $k\ge 1$, and set $T=\sum_j w_jx_j^k$. Among nonnegative integer multiplicities $m_j$ with a convergent unweighted sum and weighted sum $\sum_j m_jw_jx_j^k=T$, the unweighted sum $\sum_j m_jw_j$ has unique minimum $S$, attained by $m_j=1$ everywhere. For every nonnegative prefix length $J$ and real $y$, such multiplicities with the first $J$ entries equal to one and both sums converging to $y$ and $T$, respectively, exist if and only if $y\ge S$.
-- source:
--   Erdős problem 68, https://www.erdosproblems.com/68. Related background on the irrationality question includes Will Cook, Integer Linear Forms for a Factorial Reciprocal Series, https://github.com/wcook04/plectis-erdos/blob/main/docs/papers/full-text/erdos-68-factorial-denominator-irrationality.md, and Open Proof Network, https://openproofnetwork.org/problems/erdos-68/. Matt directed the investigation. OpenAI Codex (Astra) developed this construction and Lean proof using Mathlib.

import Mathlib

theorem Erdos68.fixed_weight_minimum_and_range (k : ℕ) (hk : 1 ≤ k) :
    let w : ℕ → ℝ := fun i => 1 / ((i + 2).factorial - 1 : ℝ)
    let x : ℕ → ℝ := fun i => 1 / ((i + 2).factorial : ℝ)
    let S : ℝ := ∑' i, w i
    let T : ℝ := ∑' i, w i * x i ^ k
    (∀ m : ℕ → ℕ, Summable (fun i => (m i : ℝ) * w i) →
      (∑' i, (m i : ℝ) * w i * x i ^ k) = T →
      (∃ i, m i ≠ 1) → S < ∑' i, (m i : ℝ) * w i) ∧
    (∀ (J : ℕ) (y : ℝ),
      (∃ m : ℕ → ℕ, (∀ i < J, m i = 1) ∧
        HasSum (fun i => (m i : ℝ) * w i) y ∧
        HasSum (fun i => (m i : ℝ) * (w i * x i ^ k)) T) ↔ S ≤ y) := by sorry
