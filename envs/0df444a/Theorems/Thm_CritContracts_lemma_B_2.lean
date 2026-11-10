-- Prove2me | Theorems.Thm_CritContracts_lemma_B_2
-- name    : CritContracts.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:01.85964+00:00
-- url     : https://prove2.me/theorems/1ae34329-6962-4729-a4b0-365bdd52af05
-- title:
--   Lemma B.2 — the three-edge path transmits its value exactly when its source is active
-- statement:
--   Consider one three-edge path $s-z-y-t$ of value $M$ from $s$ to $t$ in the reduction's graph (a state path from $q_j$ to $p_i$ or from $p_j$ to $q_i$, or one of the final paths from $r_1$ to $a$ and from $r_0$ to $b$). Let $\lambda\in\mathbb R^2_+$, let $\lambda_s$ and $\lambda_t$ denote the payment coordinates on the sides of $s$ and $t$, and suppose $\lambda_s+\lambda_t\le1+\varepsilon$.
--
--   1. If $s,t\in S(\lambda)$ and $\lambda_s,\lambda_t\ge\tfrac12-4\Delta$, then $y,z\in S(\lambda)$, and the edge of weight $M$ incident to $t$ is active.
--   2. If $s\notin S(\lambda)$ and $\lambda_t\ge\tfrac12-4\Delta$, then $y\notin S(\lambda)$, and the edge of weight $M$ incident to $t$ is inactive.
--
--   The gadget simulates a directed edge from $s$ to $t$ in a game where both agents share the same reward.
--
--
--   **Formalization Note** The Subset Sum instance is a list `ws` of positive weights with target `T`, $k\ge1$ and $1\le T\le W-1$; $S(\lambda)$ is the union of the $\lambda$-stable profiles of the auxiliary instance (`auxInst ws T`). Items are $0,\dots,k-1$ in Lean and $1,\dots,k$ in the paper. The edge of weight $M$ incident to $t$ is $yt$; it is active when $y$ and $t$ are both in $S(\lambda)$.
--
--   Differences from the source:
--
--   - encoding: a Subset Sum instance with positive integer weights w₁, …, w_k and target T, assumed WLOG to have k ≥ 1 and 1 ≤ T ≤ W − 1 (p.33) → ws : List ℕ, T : ℕ with SSRange ws T; reason: the standing assumption of Appendix B.1.1 written as a hypothesis
--   - reading: λ (the lemma's payment vector) → λ ∈ ℝ²₊, i.e. 0 ≤ λ₁, 0 ≤ λ₂; reason: p.33: the reduction uses payment vectors λ = (λ₁, λ₂) ∈ ℝ²₊
--   - encoding: real edge weights and costs → rationals cast to ℝ; reason: every number of the construction is rational; same instance
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Lemma B.2, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_CritContracts_Construction

set_option autoImplicit false

namespace CritContracts

open Construction

/-- **Lemma B.2** (Ezra–Feldman–Molina–Schlesinger, *Sources of Complexity in Multi-Agent Combinatorial Contracts*,
STOC 2027 submission (manuscript sha256 430be35c…), Appendix B.1.1, p.35, PDF p.36): consider one three-edge path
`s − z − y − t` of value `M` from `s` to `t` in the construction of Appendix B.1.1. Let `λ_s` and
`λ_t` be the payment coordinates on the sides of `s` and `t`, and suppose `λ_s + λ_t ≤ 1 + ε`.
1. If `s, t ∈ S(λ)` and `λ_s, λ_t ≥ 1/2 − 4Δ`, then `y, z ∈ S(λ)`, and the edge of weight `M`
   incident to `t` is active.
2. If `s ∉ S(λ)` and `λ_t ≥ 1/2 − 4Δ`, then `y ∉ S(λ)`, and the edge of weight `M` incident to
   `t` is inactive.

**Formalization Note** The Subset Sum instance has positive integer weights \`ws = [w₁, …, w_k]\` and target \`T\` with
\`k ≥ 1\` and \`1 ≤ T ≤ W − 1\` (the "without loss of generality" of p.33, \`SSRange\`). `S(λ)` is `(auxInst ws T).stableUnion λ` and `λ ∈ ℝ²₊`. The paths
are the state paths (`qp`, `pq`) and the two final paths (`ra`, `rb`). The edge of weight `M`
incident to `t` is `yt`; it is active when both `y` and `t` are in `S(λ)`. Items are \`0, …, k − 1\` here and \`1, …, k\` in the paper. -/
theorem lemma_B_2 (ws : List ℕ) (T : ℕ) (hWLOG : SSRange ws T) (π : PathIx ws.length)
    (lam : Fin 2 → ℝ) (hlam : ∀ s, 0 ≤ lam s)
    (hsum : lam π.srcSide + lam (1 - π.srcSide) ≤ 1 + (epsPar ws : ℝ)) :
    (π.src ∈ (auxInst ws T).stableUnion lam → π.tgt ∈ (auxInst ws T).stableUnion lam →
        1 / 2 - 4 * (Delta ws : ℝ) ≤ lam π.srcSide → 1 / 2 - 4 * (Delta ws : ℝ) ≤ lam (1 - π.srcSide) →
        Node.y π ∈ (auxInst ws T).stableUnion lam ∧ Node.z π ∈ (auxInst ws T).stableUnion lam ∧
          (Node.y π ∈ (auxInst ws T).stableUnion lam ∧ π.tgt ∈ (auxInst ws T).stableUnion lam)) ∧
    (π.src ∉ (auxInst ws T).stableUnion lam →
        1 / 2 - 4 * (Delta ws : ℝ) ≤ lam (1 - π.srcSide) →
        Node.y π ∉ (auxInst ws T).stableUnion lam ∧
          ¬ (Node.y π ∈ (auxInst ws T).stableUnion lam ∧ π.tgt ∈ (auxInst ws T).stableUnion lam)) := by sorry

end CritContracts
