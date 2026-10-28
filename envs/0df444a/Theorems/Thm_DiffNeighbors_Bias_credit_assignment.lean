-- Prove2me | Theorems.Thm_DiffNeighbors_Bias_credit_assignment
-- name    : DiffNeighbors.Bias.credit_assignment
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T08:41:22.318629+00:00
-- url     : https://prove2.me/theorems/d67ae134-85c9-4823-8f50-149c9fa12bea
-- title:
--   Equation (5), §3, p. 8 — credit assignment: the DN estimator equals (1/N) Σ_i (η_i + ξ_i Σ_{j∈N_i} η_j) Y_i
-- statement:
--   Consider $N$ units with interference graph $G$ (neighbourhoods $\mathcal N_i$), outcome functions $f_i$ and observed outcomes $Y_i = f_i(z)$ at a treatment vector $z \in \{0,1\}^N$. For $p \in \mathbb R$ write
--   $$\eta_i = \frac{z_i}{p} - \frac{1 - z_i}{1 - p}, \qquad \xi_i = \frac{z_i(1-p)}{p} + \frac{(1 - z_i)p}{1 - p}.$$
--   The DN estimator (3), $\mathrm{ATE}_{\mathrm{DN}} = \frac1N \sum_i \eta_i \bigl(\sum_{j \in \mathcal N_i} Y_j \xi_j + Y_i\bigr)$, can be rewritten as assigning credit for each outcome $Y_i$ to the treatments of $i$ and of its neighbours:
--   $$\mathrm{ATE}_{\mathrm{DN}} = \frac1N \sum_{i=1}^N \Bigl(\eta_i + \xi_i \sum_{j \in \mathcal N_i} \eta_j\Bigr) Y_i. \tag{5}$$
--
--   The paper uses this form in the analysis of the estimator's expectation and variance: each outcome enters once, with a weight built from the treatments that influence it.
--
--   Differences from the source:
--   - generalization: p ∈ (0,1) and outcomes under Assumption 1 (standing) → any real p and any outcome functions f, with no Assumption 1; reason: the identity is a rearrangement of a finite double sum that uses only the symmetry of the graph; it specializes to the paper's setting
--   - encoding: units [N] = {1,…,N}, treatment vectors z ∈ {0,1}^N, an undirected graph without self-loops, d = max_i |N_i| → a finite type ι with N = card ι, z : ι → Bool with 1/0 read through ind, G : SimpleGraph ι, N_i = G.neighborFinset i, d = G.maxDegree; reason: a simple graph is exactly an undirected graph without self-loops; same instances
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, p. 8, §3, Credit Assignment, (5)

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Model

namespace DiffNeighbors.Bias

open Finset

/-- **Credit assignment**, (5), §3, p. 8: the DN estimator (3) equals
`(1/N) ∑_i (η_i + ξ_i ∑_{j ∈ N_i} η_j) Y_i`, with `η_j = z_j/p − (1 − z_j)/(1 − p)`. -/
theorem credit_assignment {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [DecidableRel G.Adj] (p : ℝ) (f : ι → (ι → Bool) → ℝ) (z : ι → Bool) :
    dnEstimator G p f z = (Fintype.card ι : ℝ)⁻¹ *
      ∑ i, (eta p z i + xi p z i * ∑ j ∈ G.neighborFinset i, eta p z j) * f i z := by sorry

end DiffNeighbors.Bias
