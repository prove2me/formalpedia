-- Prove2me | Theorems.Thm_DistortedCondExp_exists_distortion_interp
-- name    : DistortedCondExp.exists_distortion_interp
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:59:42.068165+00:00
-- url     : https://prove2.me/theorems/e8270924-19d5-4998-86b0-4d30835e88d7
-- title:
--   A distortion function carrying the conditional survival probabilities under $\mathbb P$ to those under $\mathbb Q$
-- statement:
--   Throughout, $X$ is the recombining binomial tree of (3.11): nodes $x_{i,0}<\dots<x_{i,i}$ at time $t_i$ ($0\le i\le N$), up-probabilities $0<p^+_{i,j}<1$; $\varphi_{t_1},\dots,\varphi_{t_N}$ are distortion functions and $\varphi_{t_0}(p)=p$; $G_{i,j}=\mathbb P(X_{t_i}\ge x_{i,j})$, $G_{i,i+1}=0$; $q^\pm_{i,j}$ and $\mathbb Q$ are given by (3.13) and (3.15); and condition (3.14) holds.
--
--   For all $0\le i<n\le N$ and $0\le j\le i$ there is a distortion function $f$ such that
--   $$
--   f\bigl(\mathbb P\{X_{t_n}\ge x_{n,k}\mid X_{t_i}=x_{i,j}\}\bigr)=\mathbb Q\{X_{t_n}\ge x_{n,k}\mid X_{t_i}=x_{i,j}\}\qquad\text{for all }0\le k\le n .
--   $$
--
--   This is the local construction of the dynamic distortion function $\Phi(t_i,t_n,x_{i,j};\cdot)$ in the existence part of Theorem 3.4.
--
--   **Formalization Note** Both sides are strictly decreasing in $k$ only on the reachable range $j<k\le j+n-i$; for $k\le j$ both equal $1$ and for $k>j+n-i$ both equal $0$. The statement covers every $0\le k\le n$.
--
--   Differences from the source:
--   - encoding: a Markov process X on an abstract filtered probability space with transition law (3.11) and the filtration F = F^X it generates → the canonical path space Fin N → Bool (true = up) with path weights ∏ p^±, and X_{t_i}(ω) = x_{i, number of up-moves before i}; reason: every quantity in the statement depends only on the law of X and on F^X; the same instances
--   - encoding: times 0 = t_0 < ⋯ < t_N → time indices 0, …, N (Φ(t_i, t_n, x; p) is Φ i n x p, φ_{t_n} is φ n); reason: the times enter only as labels
--   - encoding: the assumption φ_0(p) := p → phiExt φ 0 = id built into the definitions; the value φ 0 of the given family is ignored; reason: the same convention, without a hypothesis on φ 0
--   - reading: "one can easily define a function Φ … so that (3.17) holds" and "one may extend Φ to all p ∈ [0, 1] by linear interpolation. Then … Φ(t_i, t_n, x_{i,j}; ·) satisfies Definition 2.1 (i)" → there exists a distortion function f with f(ℙ{…}) = ℚ{…} for all 0 ≤ k ≤ n; reason: the page's claim is that such a function can be defined; the linear interpolant is one witness
-- source:
--   Ma–Wong–Zhang, Time-consistent conditional expectation under probability distortion, arXiv:1809.08262v5, https://arxiv.org/abs/1809.08262v5, proof of Theorem 3.4, first paragraph and "linear interpolation" remark, p.14

import Mathlib
import Definitions.Def_DistortedCondExp_Distortion
import Definitions.Def_DistortedCondExp_Tree
import Definitions.Def_DistortedCondExp_Dynamic

open MeasureTheory Set

namespace DistortedCondExp

/-- **A distortion function matching the conditional survival probabilities** (Ma–Wong–Zhang,
arXiv:1809.08262v5, proof of Theorem 3.4, p.14: "both `ℙ{X_{t_n} ≥ x_{n,k} | X_{t_i} = x_{i,j}}` and
`ℚ{X_{t_n} ≥ x_{n,k} | X_{t_i} = x_{i,j}}` are strictly decreasing in `k` … Then one can easily
define a function `Φ`, depending on `t_i, t_n, x_{i,j}`, so that (3.17) holds for all `x_{n,k}`,
`0 ≤ k ≤ n`", and "one may extend `Φ` to all `p ∈ [0, 1]` by linear interpolation. Then by (3.17)
it is straightforward to show that `Φ(t_i, t_n, x_{i,j}; ·)` satisfies Definition 2.1 (i)").
Under (3.14), for all `0 ≤ i < n ≤ N` and `0 ≤ j ≤ i` there is a distortion function `f` with
`f(ℙ{X_{t_n} ≥ x_{n,k} | X_{t_i} = x_{i,j}}) = ℚ{X_{t_n} ≥ x_{n,k} | X_{t_i} = x_{i,j}}` for all
`0 ≤ k ≤ n`.

**Formalization Note** Both conditional survival probabilities are strictly decreasing in `k` only
on the reachable range `j < k ≤ j + n − i`; for `k ≤ j` both equal `1` and for `k > j + n − i`
both equal `0`. The statement covers every `0 ≤ k ≤ n`, as (3.17) does. -/
theorem exists_distortion_interp (N : ℕ) (x p : ℕ → ℕ → ℝ) (φ : ℕ → ℝ → ℝ)
    (htree : IsBinomialTree N x p) (hφ : ∀ n, 1 ≤ n → n ≤ N → IsDistortion (φ n))
    (h314 : Cond314 N x p φ) :
    ∀ i n j, i < n → n ≤ N → j ≤ i → ∃ f : ℝ → ℝ, IsDistortion f ∧
      ∀ k, k ≤ n →
        f (cprob p {ω : Path N | x n k ≤ X x n ω} {ω : Path N | X x i ω = x i j}) =
          cprob (qPlus N x p φ) {ω : Path N | x n k ≤ X x n ω} {ω : Path N | X x i ω = x i j} := by sorry

end DistortedCondExp
