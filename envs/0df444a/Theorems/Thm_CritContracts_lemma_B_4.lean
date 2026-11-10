-- Prove2me | Theorems.Thm_CritContracts_lemma_B_4
-- name    : CritContracts.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:20.8153+00:00
-- url     : https://prove2.me/theorems/53e8244b-ba16-48c8-93ca-b72cf0ae1387
-- title:
--   Lemma B.4 — exact encoding: on $I_\sigma$ the active state vertices are exactly the $\sigma$-states
-- statement:
--   Let $\sigma\in\{0,1\}^k$, $x\in I_\sigma$, and set $\lambda=(x,1-x)$, where
--   $$Q(\sigma)=\sum_{i:\sigma_i=1}2\cdot3^{-i},\qquad I_\sigma=\Bigl[\tfrac12+\Delta Q(\sigma)+\tfrac{\Delta L}4,\ \tfrac12+\Delta Q(\sigma)+\tfrac{3\Delta L}4\Bigr].$$
--   Among the state vertices, $S(\lambda)$ contains exactly
--   $$\{p_i:\sigma_i=0\}\cup\{q_i:\sigma_i=1\}.$$
--
--   So the $2^k$ intervals $I_\sigma$ on the line $\lambda_1+\lambda_2=1$ encode the $2^k$ subsets of items: $q_i$ active means item $i$ is chosen.
--
--
--   **Formalization Note** The Subset Sum instance is a list `ws` of positive weights with target `T`, $k\ge1$ and $1\le T\le W-1$; $S(\lambda)$ is the union of the $\lambda$-stable profiles of the auxiliary instance (`auxInst ws T`). Items are $0,\dots,k-1$ in Lean and $1,\dots,k$ in the paper. $\sigma_i=1$ is `σ i = true`, and $Q(\sigma)$ is `Qmass σ` $=\sum_{\sigma_i}2\cdot3^{-(i+1)}$ with 0-based items.
--
--   Differences from the source:
--
--   - encoding: a Subset Sum instance with positive integer weights w₁, …, w_k and target T, assumed WLOG to have k ≥ 1 and 1 ≤ T ≤ W − 1 (p.33) → ws : List ℕ, T : ℕ with SSRange ws T; reason: the standing assumption of Appendix B.1.1 written as a hypothesis
--   - encoding: items i ∈ [k] = {1, …, k} → i : Fin k, item i of Lean is item i + 1 of the paper (3^{−i} is tern i = 3^{−(i+1)}); reason: Lean convention; same instances
--   - encoding: real edge weights and costs → rationals cast to ℝ; reason: every number of the construction is rational; same instance
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Lemma B.4, p.35 (PDF p.36); Q(σ) and I_σ, p.35

import Mathlib
import Definitions.Def_CritContracts_Construction

set_option autoImplicit false

namespace CritContracts

open Construction

/-- **Lemma B.4** (Ezra–Feldman–Molina–Schlesinger, *Sources of Complexity in Multi-Agent Combinatorial Contracts*,
STOC 2027 submission (manuscript sha256 430be35c…), Appendix B.1.1, p.35, PDF p.36): let `σ ∈ {0,1}^k`, `x ∈ I_σ`, and set
`λ = (x, 1 − x)`. Among the state vertices, `S(λ)` contains exactly
`{p_i : σ_i = 0} ∪ {q_i : σ_i = 1}`.

Here `Q(σ) = Σ_{i : σ_i = 1} 2·3^{−i}` and
`I_σ = [1/2 + ΔQ(σ) + ΔL/4, 1/2 + ΔQ(σ) + 3ΔL/4]` (p.35).

**Formalization Note** The Subset Sum instance has positive integer weights \`ws = [w₁, …, w_k]\` and target \`T\` with
\`k ≥ 1\` and \`1 ≤ T ≤ W − 1\` (the "without loss of generality" of p.33, \`SSRange\`). `σ_i = 1` is `σ i = true`. Items are \`0, …, k − 1\` here and \`1, …, k\` in the paper., so `Q(σ)` is
`Σ_{σ i} 2·3^{−(i+1)}` (`Qmass`). -/
theorem lemma_B_4 (ws : List ℕ) (T : ℕ) (hWLOG : SSRange ws T)
    (σ : Fin ws.length → Bool) (x : ℝ) (hx : x ∈ encInterval ws σ) (i : Fin ws.length) :
    (Node.p i ∈ (auxInst ws T).stableUnion (linePay x) ↔ σ i = false) ∧
    (Node.q i ∈ (auxInst ws T).stableUnion (linePay x) ↔ σ i = true) := by sorry

end CritContracts
