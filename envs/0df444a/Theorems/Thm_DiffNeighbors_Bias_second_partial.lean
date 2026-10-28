-- Prove2me | Theorems.Thm_DiffNeighbors_Bias_second_partial
-- name    : DiffNeighbors.Bias.second_partial
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T08:41:27.858319+00:00
-- url     : https://prove2.me/theorems/e9f3cef6-08b4-4cb7-8950-59b5fe5b2b75
-- title:
--   §3.3, p. 11 — ∂²F/∂w_j∂w_k = E[Δ_jk h(Z)] for j ≠ k, and ∂²F/∂w_j² = 0
-- statement:
--   Let $h : \{0,1\}^N \to \mathbb R$ with multilinear extension $F$, and write
--   $$D_j(w) = \mathbb E_w[h(Z) \mid Z_j = 1] - \mathbb E_w[h(Z) \mid Z_j = 0]$$
--   for the first partial derivative $\partial F / \partial w_j$, where $\mathbb E_w$ is the expectation under independent $Z_l \sim \mathrm{Bernoulli}(w_l)$, extended multilinearly to all $w \in \mathbb R^N$. Then for every $w$:
--
--   1. for $j \neq k$,
--   $$\frac{\partial^2 F}{\partial w_j \partial w_k}(w) = \mathbb E_w[h(Z) \mid Z_j = 1, Z_k = 1] + \mathbb E_w[h(Z) \mid Z_j = 0, Z_k = 0] - \mathbb E_w[h(Z) \mid Z_j = 1, Z_k = 0] - \mathbb E_w[h(Z) \mid Z_j = 0, Z_k = 1] = \mathbb E_w[\Delta_{jk} h(Z)];$$
--   2. $\dfrac{\partial^2 F}{\partial w_j^2} = 0$.
--
--   So the Hessian of $F$ has the expected second-order finite differences off the diagonal and zeros on it; the proof of Theorem 1 bounds the Taylor remainder through these entries.
--
--   **Formalization Note** The second derivative is the derivative of $D_j$ in the coordinate $w_k$, stated as `HasDerivAt` of $t \mapsto D_j(w \text{ with } w_k := t)$ at $t = w_k$, with $D_j$ written out as the difference of the two multilinear extensions.
--
--   Differences from the source:
--   - generalization: F^a of node i, for j, k ∈ N_i → the multilinear extension of any h : {0,1}^ι → ℝ, at any w ∈ ℝ^ι, for all coordinates j, k; reason: specializes with h = condOutcome f i a and j, k ∈ N_i
--   - encoding: ∂²F/∂w_j∂w_k and E[Δ_jk f^a(Z)] → HasDerivAt in the k-th coordinate of the first partial D_j of first_partial, with value mlExt (secondDiff h j k) w; reason: the mixed partial derivative; E_w[Δ_jk h(Z)] equals the four conditional expectations by linearity and independence
--   - encoding: units [N] = {1,…,N}, treatment vectors z ∈ {0,1}^N, an undirected graph without self-loops, d = max_i |N_i| → a finite type ι with N = card ι, z : ι → Bool with 1/0 read through ind, G : SimpleGraph ι, N_i = G.neighborFinset i, d = G.maxDegree; reason: a simple graph is exactly an undirected graph without self-loops; same instances
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, p. 11, §3.3 (proof of Theorem 1), display '∂²F^a/∂w_j∂w_k = … = E[Δ_jk f^a(Z)] for j, k ∈ N_i and j ≠ k, and ∂²F/∂w_j² = 0 for j = k'

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Model

namespace DiffNeighbors.Bias

open Finset

/-- **Second partial derivatives of the multilinear extension**, §3.3, p. 11. Write
`D_j(w) = E_w[h(Z) | Z_j = 1] − E_w[h(Z) | Z_j = 0]` for the first partial derivative `∂F/∂w_j`
(p. 10). Then (i) for `j ≠ k`, `∂²F/∂w_j∂w_k (w) = E_w[Δ_jk h(Z)]`, and (ii) `∂²F/∂w_j² = 0`. -/
theorem second_partial {ι : Type*} [Fintype ι] [DecidableEq ι] (h : (ι → Bool) → ℝ) (w : ι → ℝ)
    (j : ι) :
    (∀ k, j ≠ k →
      HasDerivAt (fun t => mlExt (fun z => h (Function.update z j true)) (Function.update w k t)
          - mlExt (fun z => h (Function.update z j false)) (Function.update w k t))
        (mlExt (fun z => secondDiff h j k z) w) (w k)) ∧
    HasDerivAt (fun t => mlExt (fun z => h (Function.update z j true)) (Function.update w j t)
        - mlExt (fun z => h (Function.update z j false)) (Function.update w j t))
      0 (w j) := by sorry

end DiffNeighbors.Bias
