-- Prove2me | Theorems.Thm_DenseMatching_IPM_lemma_2_3
-- name    : DenseMatching.IPM.lemma_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:40:32.428337+00:00
-- url     : https://prove2.me/theorems/3bdf3542-6650-421c-b5f2-00d6b6b24701
-- title:
--   Lemma 2.3 — independent effective-resistance sampling gives L(H) ≈_{10⁻³} L(G) with probability 1 − n⁻¹⁴ (n asymptotic)
-- statement:
--   (Spielman–Srivastava; Theorem 1.1 of Tropp.) With the paper's convention that $n$ is asymptotic (p. 7): there is $n_0$ such that for every $n\ge n_0$ and every weighted graph $G=(V,E,w)$ on $n$ vertices with positive weights, the following holds. Let $p\in(0,1]^E$ with
--   $$p_e\ge\min\{1,\ 10^8\ln n\cdot w_e R^{\rm eff}(G)_e\}\quad\text{for every edge},\qquad R^{\rm eff}(G)_e=\chi_e^\top L(G)^\dagger\chi_e .$$
--   The graph $H$ formed by keeping every edge $e$ of $G$ independently with probability $p_e$, with weight $w_e/p_e$, satisfies $L(H)\approx_{10^{-3}}L(G)$, i.e. $(1-10^{-3})L(G)\preceq L(H)\preceq(1+10^{-3})L(G)$, with probability at least $1-n^{-14}$.
--   It certifies the sparse reference $\tilde L$ of every refresh.
--
--   Differences from the source:
--   - reading: 'Throughout we treat n as asymptotic: every inequality that needs n larger than a constant is assumed' (p. 7) → ∃ n₀, ∀ n ≥ n₀; reason: the paper's standing convention for its imported lemmas
--   - generalization: a graph G = (V, E, w) (no duplicate edges, p. 7) → a published WGraph on Fin n: positive weights, no loops, parallel edges allowed; reason: the matrix-concentration argument does not use simplicity; a simple graph is the special case without parallel edges
--   - encoding: probability over the independent retention of the edges → sampleProb p (failure event) ≤ 1/n^14; reason: the product-Bernoulli probability as an explicit finite sum
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), p. 9, Lemma 2.3

import Mathlib
import Definitions.Def_EffResSparsify_Sampling_Defs
import Definitions.Def_DenseMatching_IPM_Tools

open EffResSparsify.Sampling

namespace DenseMatching.IPM

/-- Lemma 2.3 (p. 9; Spielman–Srivastava, Theorem 1.1 of Tropp), with the paper's convention that
`n` is asymptotic (p. 7). There is `n₀` such that for every `n ≥ n₀` and every weighted graph `G`
on `n` vertices: if `p ∈ (0, 1]^E` with `p_e ≥ min{1, 10⁸ ln n · w_e Reff(G)_e}` for every edge,
`Reff(G)_e = χ_e⊤ L(G)† χ_e`, then the graph `H` that keeps every edge `e` independently with
probability `p_e`, with weight `w_e/p_e`, satisfies `L(H) ≈_{10⁻³} L(G)` with probability at least
`1 − n⁻¹⁴`. -/
theorem lemma_2_3 :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (E : Type) [Fintype E] [DecidableEq E]
      (G : WGraph (Fin n) E) (p : E → ℝ),
      (∀ e, 0 < p e ∧ p e ≤ 1) →
      (∀ e, min 1 (10 ^ 8 * Real.log n * (G.w e * G.effRes e)) ≤ p e) →
      sampleProb p (fun ω => ¬ LoewnerApprox (1 / 10 ^ 3) (sampledLaplacian G p ω) G.laplacian) ≤
        1 / (n : ℝ) ^ 14 := by sorry

end DenseMatching.IPM
