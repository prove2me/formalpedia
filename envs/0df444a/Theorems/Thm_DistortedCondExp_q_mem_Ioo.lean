-- Prove2me | Theorems.Thm_DistortedCondExp_q_mem_Ioo
-- name    : DistortedCondExp.q_mem_Ioo
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:59:39.29799+00:00
-- url     : https://prove2.me/theorems/4ff0fbb3-946c-49c8-9cf9-d23c0384c211
-- title:
--   Condition (3.14) gives $0<q^+_{i,j}<1$
-- statement:
--   Throughout, $X$ is the recombining binomial tree of (3.11): nodes $x_{i,0}<\dots<x_{i,i}$ at time $t_i$ ($0\le i\le N$), up-probabilities $0<p^+_{i,j}<1$; $\varphi_{t_1},\dots,\varphi_{t_N}$ are distortion functions and $\varphi_{t_0}(p)=p$; $G_{i,j}=\mathbb P(X_{t_i}\ge x_{i,j})$, $G_{i,i+1}=0$; $q^\pm_{i,j}$ and $\mathbb Q$ are given by (3.13) and (3.15);.
--
--   If condition (3.14),
--   $$
--   \varphi_{t_i}(G_{i,j+1})<\varphi_{t_{i+1}}(G_{i+1,j+1})<\varphi_{t_i}(G_{i,j}),\qquad 0\le j\le i\le N-1,
--   $$
--   holds, then the distorted transition probabilities of (3.13) satisfy
--   $$
--   0<q^+_{i,j}<1\qquad\text{for all }0\le j\le i\le N-1 .
--   $$
--
--   Hence $\mathbb Q$ of (3.15) is a probability under which every node of the tree is reached with positive probability, so all $\mathbb Q$-conditional quantities in the mission are well defined.
--
--   Differences from the source:
--   - encoding: a Markov process X on an abstract filtered probability space with transition law (3.11) and the filtration F = F^X it generates → the canonical path space Fin N → Bool (true = up) with path weights ∏ p^±, and X_{t_i}(ω) = x_{i, number of up-moves before i}; reason: every quantity in the statement depends only on the law of X and on F^X; the same instances
--   - encoding: times 0 = t_0 < ⋯ < t_N → time indices 0, …, N (Φ(t_i, t_n, x; p) is Φ i n x p, φ_{t_n} is φ n); reason: the times enter only as labels
--   - encoding: the assumption φ_0(p) := p → phiExt φ 0 = id built into the definitions; the value φ 0 of the given family is ignored; reason: the same convention, without a hypothesis on φ 0
--   - reading: (3.13) printed for 0 ≤ j ≤ i ≤ N; (3.14) "for all (i, j)" → 0 ≤ j ≤ i ≤ N − 1; reason: the formula (3.13) uses φ_{t_{i+1}}, which exists only for i ≤ N − 1
-- source:
--   Ma–Wong–Zhang, Time-consistent conditional expectation under probability distortion, arXiv:1809.08262v5, https://arxiv.org/abs/1809.08262v5, §3.2, after eq. (3.13), with (3.14), p.12

import Mathlib
import Definitions.Def_DistortedCondExp_Distortion
import Definitions.Def_DistortedCondExp_Tree
import Definitions.Def_DistortedCondExp_Dynamic

open MeasureTheory Set

namespace DistortedCondExp

/-- **Distorted transition probabilities lie in `(0, 1)`** (Ma–Wong–Zhang, arXiv:1809.08262v5,
§3.2, after (3.13), p.12: "in order to have `0 < q⁺_{i,j} < 1`, it suffices to (and we will)
assume that (3.14)"). On the binomial tree (3.11) with distortion functions `φ_{t_1}, …, φ_{t_N}`
and `φ_{t_0} = id`, condition (3.14) gives `0 < q⁺_{i,j} < 1` for `0 ≤ j ≤ i ≤ N − 1`, so that
`ℚ` of (3.15) is a probability charging every path.

**Formalization Note** `q⁺` is `qPlus` of (3.13) with `G_{i,i+1} = 0`; `IsBinomialTree` is (3.11)
with `x_{i,0} < ⋯ < x_{i,i}` and `0 < p⁺_{i,j} < 1`. -/
theorem q_mem_Ioo (N : ℕ) (x p : ℕ → ℕ → ℝ) (φ : ℕ → ℝ → ℝ)
    (htree : IsBinomialTree N x p) (hφ : ∀ n, 1 ≤ n → n ≤ N → IsDistortion (φ n))
    (h314 : Cond314 N x p φ) :
    ∀ i j, j ≤ i → i < N → 0 < qPlus N x p φ i j ∧ qPlus N x p φ i j < 1 := by sorry

end DistortedCondExp
