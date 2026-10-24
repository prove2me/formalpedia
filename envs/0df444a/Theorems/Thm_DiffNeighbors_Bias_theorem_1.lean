-- Prove2me | Theorems.Thm_DiffNeighbors_Bias_theorem_1
-- name    : DiffNeighbors.Bias.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T08:41:21.523756+00:00
-- url     : https://prove2.me/theorems/29beea90-a253-4b04-a5c7-f5b87db4ab1b
-- title:
--   Theorem 1, p. 9 — if every conditional outcome function is ϵ-smooth, the DN estimator's bias is at most d²ϵ
-- statement:
--   Consider $N$ units with an undirected interference graph $G$ without self-loops, maximum degree $d = \max_i |\mathcal N_i|$, and potential outcome functions $f_i : \{0,1\}^N \to \mathbb R$ satisfying **Assumption 1** (neighborhood interference: $f_i(z)$ depends only on $z_i$ and $(z_j)_{j \in \mathcal N_i}$). Treatments are assigned by the Bernoulli design, $z_i$ i.i.d. Bernoulli$(p)$ with $0 < p < 1$. Let
--   $$\mathrm{ATE} = \frac1N \sum_{i=1}^N \bigl(f_i(\vec 1) - f_i(\vec 0)\bigr)$$
--   and let $\mathrm{ATE}_{\mathrm{DN}}$ be the Differences-in-Neighbors estimator (3). Suppose that the conditional outcome functions $f^1_i$ and $f^0_i$ are $\epsilon$-smooth for all nodes $i$, i.e. $|\Delta_{jk} f^a_i(z)| \le \epsilon$ for all $a$, $z$, $j$, $k$. Then
--   $$\bigl|\mathrm{ATE} - \mathbb E[\mathrm{ATE}_{\mathrm{DN}}]\bigr| \le d^2 \epsilon.$$
--
--   The bound is second order in the strength of interference: under the paper's outcome model with interference magnitude $\delta$ it gives bias $O(d^2\delta^2)$ (Corollary 1), against first order $\Theta(d\delta)$ for the difference-in-means estimator, while the DN estimator's variance stays polynomial in $d$.
--
--   Differences from the source:
--   - encoding: units [N] = {1,…,N}, treatment vectors z ∈ {0,1}^N, an undirected graph without self-loops, d = max_i |N_i| → a finite type ι with N = card ι, z : ι → Bool with 1/0 read through ind, G : SimpleGraph ι, N_i = G.neighborFinset i, d = G.maxDegree; reason: a simple graph is exactly an undirected graph without self-loops; same instances
--   - encoding: E[·] over z_i i.i.d. Bernoulli(p) → bernExp p h = Σ_z (Π_j (p if z_j = 1 else 1 − p)) h(z), a finite sum; reason: the law of the design on the finite set {0,1}^N; same values
--   - encoding: a Bernoulli(p) design whose weights divide by p and 1 − p → hypotheses 0 < p and p < 1; reason: the weights 1/p and 1/(1 − p) and the design presuppose p ∈ (0,1); this only excludes undefined cases
--   - encoding: Assumption 1, stated "throughout this work" (p. 5) → an explicit hypothesis hf : NeighborhoodInterference G f; reason: a standing assumption of the paper made explicit; Theorem 1 is false without it
--   - encoding: f^a_i as a function of z_{N_i}; E[f^a(Z) | Z_j = b] and E[f^a(Z) | Z_j = b, Z_k = c] → condOutcome f i a z = f_i(z with z_i := a), a function on all of {0,1}^N; conditional expectations are bernExp of the function with the conditioned coordinates overwritten by Function.update; reason: under Assumption 1 condOutcome f i a depends only on z_{N_i}; by independence of the coordinates, conditioning on Z_j = b is the same as setting z_j := b
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, p. 9, Theorem 1 (with §2.1, Assumption 1, p. 5; (3), p. 7; ϵ-smoothness, p. 9)

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Model

namespace DiffNeighbors.Bias

open Finset

/-- **Theorem 1** (Peng–Ye–Zheng, arXiv:2503.02271v1, p. 9). Under neighborhood interference
(Assumption 1, standing throughout the paper) and the Bernoulli(`p`) design, if every conditional
outcome function `f^1_i`, `f^0_i` is `ε`-smooth, then the bias of the DN estimator is at most `d²ε`,
where `d = max_i |N_i|` is the maximum degree of the interference graph. -/
theorem theorem_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (f : ι → (ι → Bool) → ℝ) (hf : NeighborhoodInterference G f)
    (p ε : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hε : ∀ i, ∀ a : Bool, IsSmooth ε (condOutcome f i a)) :
    |ate f - bernExp p (dnEstimator G p f)| ≤ (G.maxDegree : ℝ) ^ 2 * ε := by sorry

end DiffNeighbors.Bias
