-- Prove2me | Theorems.Thm_DiffNeighbors_Bias_first_partial
-- name    : DiffNeighbors.Bias.first_partial
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T08:41:20.736464+00:00
-- url     : https://prove2.me/theorems/4002ea80-6e61-4afc-83c9-e2b1e5584893
-- title:
--   §3.3, p. 10 — the partial derivative ∂F/∂w_j of the multilinear extension is E[h(Z)|Z_j = 1] − E[h(Z)|Z_j = 0]
-- statement:
--   Let $h : \{0,1\}^N \to \mathbb R$ and let
--   $$F(w) = \sum_{z \in \{0,1\}^N} \Bigl(\prod_{l} \bigl(z_l w_l + (1 - z_l)(1 - w_l)\bigr)\Bigr) h(z), \qquad w \in \mathbb R^N,$$
--   be its multilinear extension, which for $w \in [0,1]^N$ is $\mathbb E_w[h(Z)]$ with independent $Z_l \sim \mathrm{Bernoulli}(w_l)$. For every coordinate $j$ and every $w$,
--   $$\frac{\partial F}{\partial w_j}(w) = \mathbb E_w[h(Z) \mid Z_j = 1] - \mathbb E_w[h(Z) \mid Z_j = 0],$$
--   where $\mathbb E_w[h(Z) \mid Z_j = b]$ is the multilinear extension, at $w$, of $z \mapsto h(z \text{ with } z_j := b)$.
--
--   In the proof of Theorem 1 this is applied to $h = f^1_i$ (and $f^0_i$): it identifies the gradient term of the first-order Taylor approximation of $F^1(1)$ around $F^1(p)$.
--
--   **Formalization Note** The partial derivative is stated as `HasDerivAt` of $t \mapsto F(w \text{ with } w_j := t)$ at $t = w_j$.
--
--   Differences from the source:
--   - generalization: F¹ of node i, a function of the |N_i| neighbour treatments → the multilinear extension of any h : {0,1}^ι → ℝ, at any w ∈ ℝ^ι, for any coordinate j; reason: specializes with h = condOutcome f i true, which under Assumption 1 depends only on z_{N_i}, so its extension is the paper's F¹
--   - encoding: ∂F/∂w_j and E[f¹(Z)|Z_j = b] → HasDerivAt of t ↦ mlExt h (update w j t) at w j, with value mlExt (h ∘ update · j true) w − mlExt (h ∘ update · j false) w; reason: the partial derivative of F in its j-th coordinate; conditioning on Z_j = b sets z_j := b by independence
--   - encoding: units [N] = {1,…,N}, treatment vectors z ∈ {0,1}^N, an undirected graph without self-loops, d = max_i |N_i| → a finite type ι with N = card ι, z : ι → Bool with 1/0 read through ind, G : SimpleGraph ι, N_i = G.neighborFinset i, d = G.maxDegree; reason: a simple graph is exactly an undirected graph without self-loops; same instances
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, p. 10, §3.3 (proof of Theorem 1), display '∂F¹/∂w_j = … = E[f¹(Z)|Z_j = 1] − E[f¹(Z)|Z_j = 0]'

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Model

namespace DiffNeighbors.Bias

open Finset

/-- **First partial derivative of the multilinear extension**, §3.3, p. 10:
`∂F/∂w_j (w) = E_w[h(Z) | Z_j = 1] − E_w[h(Z) | Z_j = 0]`, where `E_w` is the expectation under
independent Bernoulli(`w_l`) coordinates. -/
theorem first_partial {ι : Type*} [Fintype ι] [DecidableEq ι] (h : (ι → Bool) → ℝ) (w : ι → ℝ)
    (j : ι) :
    HasDerivAt (fun t => mlExt h (Function.update w j t))
      (mlExt (fun z => h (Function.update z j true)) w
        - mlExt (fun z => h (Function.update z j false)) w) (w j) := by sorry

end DiffNeighbors.Bias
