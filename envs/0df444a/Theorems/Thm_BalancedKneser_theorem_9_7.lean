-- Prove2me | Theorems.Thm_BalancedKneser_theorem_9_7
-- name    : BalancedKneser.theorem_9_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:44:40.342205+00:00
-- url     : https://prove2.me/theorems/7abdc7df-db18-43c8-aec6-a64932c2e8dc
-- title:
--   Theorem 9.7 — rounding five subset constraints: a feasible system has a $0/1$ solution
-- statement:
--   Let $m\ge1$ and $\ell$ be integers, let $T_1,\dots,T_s\subseteq[m]$ with $s\le5$, and let $b_1,\dots,b_s$ be integers. For $x\in\mathbb R^m$ write $x(T)=\sum_{j\in T}x_j$. If the polytope
--   $$
--   \Pi=\Big\{x\in[0,1]^m:\ \sum_j x_j=\ell,\ \ x(T_i)\ge b_i\ (1\le i\le s)\Big\}
--   $$
--   is nonempty, then it contains a point of $\{0,1\}^m$.
--
--   The bound five is sharp (the source's remark after the theorem), and the theorem implies that $C_c(N,k)$ and $Y_c$ have the same four-skeleton for every radius $c$ (Corollary 9.8), an input of the radius-two comparison.
--
--   **Formalization Note** $[m]$ is $\mathrm{Fin}\,m$ and the constraints are indexed by $\mathrm{Fin}\,s$ ($s=0$ allowed); $\ell$ and the $b_i$ are integers, the points of $\Pi$ real vectors.
--
--   Differences from the source:
--   - encoding: [m], T₁, …, T_s, b₁, …, b_s → Fin m, T : Fin s → Finset (Fin m), b : Fin s → ℤ; reason: same instances
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, Theorem 9.7, p.21 (PDF p.23); proof pp.22–23 (PDF pp.24–25)

import Mathlib

namespace BalancedKneser

/-- **Theorem 9.7 (Rounding five subset constraints)** (Alipour–Jafari, arXiv:2611.04486v1,
p.21 (PDF p.23); proof pp.22–23): "Let m ≥ 1 and ℓ be integers, let T1, …, Ts ⊆ [m] with
s ≤ 5, and let b1, …, bs be integers. If the polytope
Π = { x ∈ [0, 1]^m : Σⱼ xⱼ = ℓ, x(Tᵢ) ≥ bᵢ (1 ≤ i ≤ s) } is nonempty, then it contains a point
of {0, 1}^m."

Here `x(T) = Σ_{j ∈ T} xⱼ`; `[m]` is `Fin m`, and the constraints are indexed by `Fin s`
(`s = 0` allowed). -/
theorem theorem_9_7 (m : ℕ) (hm : 1 ≤ m) (ℓ : ℤ) (s : ℕ) (hs : s ≤ 5)
    (T : Fin s → Finset (Fin m)) (b : Fin s → ℤ)
    (hPi : ∃ x : Fin m → ℝ, (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧ ∑ j, x j = ℓ ∧
      ∀ i, (b i : ℝ) ≤ ∑ j ∈ T i, x j) :
    ∃ y : Fin m → ℝ, (∀ j, y j = 0 ∨ y j = 1) ∧ ∑ j, y j = ℓ ∧
      ∀ i, (b i : ℝ) ≤ ∑ j ∈ T i, y j := by sorry

end BalancedKneser
