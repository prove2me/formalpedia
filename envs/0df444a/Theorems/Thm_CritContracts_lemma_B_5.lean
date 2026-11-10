-- Prove2me | Theorems.Thm_CritContracts_lemma_B_5
-- name    : CritContracts.lemma_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:59.513581+00:00
-- url     : https://prove2.me/theorems/923e5e5e-a094-46f6-93b1-a4124a27698e
-- title:
--   Lemma B.5 — at most one of $p_i,q_i$ is active when $\lambda_1+\lambda_2\le1+\varepsilon$
-- statement:
--   For every $\lambda\in\mathbb R^2_+$ satisfying $\lambda_1+\lambda_2\le1+\varepsilon$, and for every item $i\in[k]$, at most one of $p_i$ and $q_i$ belongs to $S(\lambda)$.
--
--   This holds on the whole feasible payment region, not only on the encoder intervals, and is what lets the soundness proof read off a subset of items from any equilibrium.
--
--
--   **Formalization Note** The Subset Sum instance is a list `ws` of positive weights with target `T`, $k\ge1$ and $1\le T\le W-1$; $S(\lambda)$ is the union of the $\lambda$-stable profiles of the auxiliary instance (`auxInst ws T`). Items are $0,\dots,k-1$ in Lean and $1,\dots,k$ in the paper.
--
--   Differences from the source:
--
--   - encoding: a Subset Sum instance with positive integer weights w₁, …, w_k and target T, assumed WLOG to have k ≥ 1 and 1 ≤ T ≤ W − 1 (p.33) → ws : List ℕ, T : ℕ with SSRange ws T; reason: the standing assumption of Appendix B.1.1 written as a hypothesis
--   - reading: λ (the lemma's payment vector) → λ ∈ ℝ²₊, i.e. 0 ≤ λ₁, 0 ≤ λ₂; reason: p.33: the reduction uses payment vectors λ = (λ₁, λ₂) ∈ ℝ²₊
--   - encoding: items i ∈ [k] = {1, …, k} → i : Fin k, item i of Lean is item i + 1 of the paper (3^{−i} is tern i = 3^{−(i+1)}); reason: Lean convention; same instances
--   - encoding: real edge weights and costs → rationals cast to ℝ; reason: every number of the construction is rational; same instance
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Lemma B.5, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_CritContracts_Construction

set_option autoImplicit false

namespace CritContracts

open Construction

/-- **Lemma B.5** (Ezra–Feldman–Molina–Schlesinger, *Sources of Complexity in Multi-Agent Combinatorial Contracts*,
STOC 2027 submission (manuscript sha256 430be35c…), Appendix B.1.1, p.35, PDF p.36): for every `λ ∈ ℝ²₊` satisfying
`λ₁ + λ₂ ≤ 1 + ε`, and for every item `i ∈ [k]`, at most one of `p_i` and `q_i` belongs to `S(λ)`.

**Formalization Note** The Subset Sum instance has positive integer weights \`ws = [w₁, …, w_k]\` and target \`T\` with
\`k ≥ 1\` and \`1 ≤ T ≤ W − 1\` (the "without loss of generality" of p.33, \`SSRange\`). `S(λ)` is `(auxInst ws T).stableUnion λ`. Items are \`0, …, k − 1\` here and \`1, …, k\` in the paper. -/
theorem lemma_B_5 (ws : List ℕ) (T : ℕ) (hWLOG : SSRange ws T)
    (lam : Fin 2 → ℝ) (hlam : ∀ s, 0 ≤ lam s) (hsum : lam 0 + lam 1 ≤ 1 + (epsPar ws : ℝ))
    (i : Fin ws.length) :
    ¬ (Node.p i ∈ (auxInst ws T).stableUnion lam ∧ Node.q i ∈ (auxInst ws T).stableUnion lam) := by sorry

end CritContracts
