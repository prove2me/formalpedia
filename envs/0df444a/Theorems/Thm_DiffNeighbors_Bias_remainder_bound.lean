-- Prove2me | Theorems.Thm_DiffNeighbors_Bias_remainder_bound
-- name    : DiffNeighbors.Bias.remainder_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T08:41:30.287344+00:00
-- url     : https://prove2.me/theorems/f98486a2-6f8f-4ae7-82b3-061a9251c772
-- title:
--   §3.3, p. 11 — |Σ_{j,k∈N_i, j≠k} (a − p)² E_{p′}[Δ_jk f^a_i(Z)]| ≤ d²ϵ for ϵ-smooth f^a_i
-- statement:
--   Let $G$ be the interference graph with maximum degree $d$, let $i$ be a unit, $a \in \{0,1\}$, $p \in [0,1]$, and let $p' \in [0,1]^N$ be any vector of treatment probabilities, with $\mathbb E_{p'}$ the expectation under independent $Z_l \sim \mathrm{Bernoulli}(p'_l)$. If the conditional outcome function $f^a_i$ is $\epsilon$-smooth, then
--   $$\Bigl|\sum_{j, k \in \mathcal N_i:\, j \neq k} (a - p)^2\, \mathbb E_{p'}[\Delta_{jk} f^a_i(Z)]\Bigr| \le d^2 \epsilon.$$
--
--   By the second-partial identity the sum is $(a - p)^\top H^a(p')(a - p)$, so with the corrected Taylor remainder this bounds the error of each first-order approximation by $\tfrac12 d^2\epsilon$, and Theorem 1 follows.
--
--   Differences from the source:
--   - reading: |(a − p)ᵀH^a(p′)(a − p)| = Σ_{j,k∈N_i: j≠k} (a − p)² E[Δ_jk f^a(Z)] ≤ d²ϵ → |Σ_{j,k∈N_i, j≠k} (a − p)² E_{p′}[Δ_jk f^a_i(Z)]| ≤ d²ϵ; reason: the absolute value printed on the left applies to the sum, and E is the expectation at p′ (the Hessian is evaluated at p′)
--   - generalization: p′ the Taylor point between (p,…,p) and (a,…,a), with ϵ-smoothness of f¹_i, f⁰_i for all nodes, under Assumption 1 → any p′ ∈ [0,1]^ι, ϵ-smoothness of the single function f^a_i, any outcome functions; reason: the bound holds for every product Bernoulli law; the Taylor point is one such vector, and the paper's hypotheses imply these
--   - encoding: p a treatment probability, p′ a vector of probabilities → hypotheses p ∈ [0,1] and p′_l ∈ [0,1] for all l; reason: outside [0,1] E_{p′} is not an expectation; these are the values the proof uses
--   - encoding: f^a_i as a function of z_{N_i}; E[f^a(Z) | Z_j = b] and E[f^a(Z) | Z_j = b, Z_k = c] → condOutcome f i a z = f_i(z with z_i := a), a function on all of {0,1}^N; conditional expectations are bernExp of the function with the conditioned coordinates overwritten by Function.update; reason: under Assumption 1 condOutcome f i a depends only on z_{N_i}; by independence of the coordinates, conditioning on Z_j = b is the same as setting z_j := b
--   - encoding: units [N] = {1,…,N}, treatment vectors z ∈ {0,1}^N, an undirected graph without self-loops, d = max_i |N_i| → a finite type ι with N = card ι, z : ι → Bool with 1/0 read through ind, G : SimpleGraph ι, N_i = G.neighborFinset i, d = G.maxDegree; reason: a simple graph is exactly an undirected graph without self-loops; same instances
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, p. 11, §3.3 (proof of Theorem 1), display '|(a − p)^⊤ H^a(p′)(a − p)| = Σ_{j,k∈N_i: j≠k} (a − p)² E[Δ_jk f^a(Z)] ≤ d²ϵ'

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Model

namespace DiffNeighbors.Bias

open Finset

/-- **Bound on the second-order term**, §3.3, p. 11: for `a ∈ {0, 1}`, `p ∈ [0, 1]`, any vector of
treatment probabilities `p′ ∈ [0, 1]^N` and an `ε`-smooth conditional outcome function `f^a_i`,
`|∑_{j,k ∈ N_i, j ≠ k} (a − p)² E_{p′}[Δ_jk f^a_i(Z)]| ≤ d²ε`, with `d` the maximum degree and `E_{p′}`
the expectation under independent Bernoulli(`p′_l`) coordinates. -/
theorem remainder_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι)
    [DecidableRel G.Adj] (f : ι → (ι → Bool) → ℝ) (i : ι) (a : Bool) (ε p : ℝ) (w : ι → ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hw : ∀ l, w l ∈ Set.Icc (0 : ℝ) 1)
    (hε : IsSmooth ε (condOutcome f i a)) :
    |∑ j ∈ G.neighborFinset i, ∑ k ∈ (G.neighborFinset i).erase j,
        (ind a - p) ^ 2 * mlExt (fun z => secondDiff (condOutcome f i a) j k z) w|
      ≤ (G.maxDegree : ℝ) ^ 2 * ε := by sorry

end DiffNeighbors.Bias
