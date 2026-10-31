-- Prove2me | Theorems.Thm_DistortedCondExp_eq_3_18
-- name    : DistortedCondExp.eq_3_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:59:32.850776+00:00
-- url     : https://prove2.me/theorems/891c7a63-7da1-4a74-a350-6f768e8f16eb
-- title:
--   Eq. (3.18): $\varphi_{t_n}(\mathbb P\{X_{t_n}\ge x_{n,k}\})=\mathbb Q\{X_{t_n}\ge x_{n,k}\}$
-- statement:
--   Throughout, $X$ is the recombining binomial tree of (3.11): nodes $x_{i,0}<\dots<x_{i,i}$ at time $t_i$ ($0\le i\le N$), up-probabilities $0<p^+_{i,j}<1$; $\varphi_{t_1},\dots,\varphi_{t_N}$ are distortion functions and $\varphi_{t_0}(p)=p$; $G_{i,j}=\mathbb P(X_{t_i}\ge x_{i,j})$, $G_{i,i+1}=0$; $q^\pm_{i,j}$ and $\mathbb Q$ are given by (3.13) and (3.15); and condition (3.14) holds.
--
--   For $0\le n\le N$ and $0\le k\le n$,
--   $$
--   \varphi_{t_n}\bigl(\mathbb P\{X_{t_n}\ge x_{n,k}\}\bigr)=\mathbb Q\{X_{t_n}\ge x_{n,k}\}. \tag{3.18}
--   $$
--
--   The distorted probability $\mathbb Q$ reproduces, at every time, the distorted survival function seen from time $0$. This is the content of the initial condition $\Phi(t_0,t_n,x_{0,0};\cdot)=\varphi_{t_n}$ of Theorem 3.4.
--
--   Differences from the source:
--   - encoding: a Markov process X on an abstract filtered probability space with transition law (3.11) and the filtration F = F^X it generates → the canonical path space Fin N → Bool (true = up) with path weights ∏ p^±, and X_{t_i}(ω) = x_{i, number of up-moves before i}; reason: every quantity in the statement depends only on the law of X and on F^X; the same instances
--   - encoding: times 0 = t_0 < ⋯ < t_N → time indices 0, …, N (Φ(t_i, t_n, x; p) is Φ i n x p, φ_{t_n} is φ n); reason: the times enter only as labels
--   - encoding: the assumption φ_0(p) := p → phiExt φ 0 = id built into the definitions; the value φ 0 of the given family is ignored; reason: the same convention, without a hypothesis on φ 0
-- source:
--   Ma–Wong–Zhang, Time-consistent conditional expectation under probability distortion, arXiv:1809.08262v5, https://arxiv.org/abs/1809.08262v5, proof of Theorem 3.4, eq. (3.18), p.14

import Mathlib
import Definitions.Def_DistortedCondExp_Distortion
import Definitions.Def_DistortedCondExp_Tree
import Definitions.Def_DistortedCondExp_Dynamic

open MeasureTheory Set

namespace DistortedCondExp

/-- **Equation (3.18)** (Ma–Wong–Zhang, arXiv:1809.08262v5, proof of Theorem 3.4, p.14): under
(3.14), `φ_{t_n}(ℙ{X_{t_n} ≥ x_{n,k}}) = ℚ{X_{t_n} ≥ x_{n,k}}` for `0 ≤ n ≤ N`, `0 ≤ k ≤ n`, with
`φ_{t_0} = id`. The paper notes that the initial condition `Φ(t_0, t_n, x_{0,0}; p) := φ_{t_n}(p)` is
equivalent to it.

**Formalization Note** `phiExt φ n` is `φ_{t_n}` with `φ_{t_0} = id`; `ℚ = prob (qPlus N x p φ)`
is the law of (3.15). -/
theorem eq_3_18 (N : ℕ) (x p : ℕ → ℕ → ℝ) (φ : ℕ → ℝ → ℝ)
    (htree : IsBinomialTree N x p) (hφ : ∀ n, 1 ≤ n → n ≤ N → IsDistortion (φ n))
    (h314 : Cond314 N x p φ) :
    ∀ n, n ≤ N → ∀ k, k ≤ n →
      phiExt φ n (prob p {ω : Path N | x n k ≤ X x n ω}) =
        prob (qPlus N x p φ) {ω : Path N | x n k ≤ X x n ω} := by sorry

end DistortedCondExp
