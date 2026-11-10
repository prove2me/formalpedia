-- Prove2me | Theorems.Thm_CritContracts_lemma_B_3
-- name    : CritContracts.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:05.260627+00:00
-- url     : https://prove2.me/theorems/ce8f1c7b-b825-4f9b-9c2e-932dcdcc8165
-- title:
--   Lemma B.3 — an active state vertex forces its side's payment to be at least $\tfrac12-4\Delta$
-- statement:
--   In the reduction's graph, for every $\lambda\in\mathbb R^2_+$ and all $i\in[k]$:
--   $$q_i\in S(\lambda)\ \Rightarrow\ \lambda_1\ge\tfrac12-4\Delta,\qquad p_i\in S(\lambda)\ \Rightarrow\ \lambda_2\ge\tfrac12-4\Delta.$$
--   No bound on $\lambda_1+\lambda_2$ is assumed.
--
--   The lemma makes Lemma B.2 applicable to every state path whose target is active.
--
--
--   **Formalization Note** The Subset Sum instance is a list `ws` of positive weights with target `T`, $k\ge1$ and $1\le T\le W-1$; $S(\lambda)$ is the union of the $\lambda$-stable profiles of the auxiliary instance (`auxInst ws T`). Items are $0,\dots,k-1$ in Lean and $1,\dots,k$ in the paper. $\lambda_1$ is the payment of agent 1 (side $U$), $\lambda_2$ that of agent 2 (side $V$).
--
--   Differences from the source:
--
--   - encoding: a Subset Sum instance with positive integer weights w₁, …, w_k and target T, assumed WLOG to have k ≥ 1 and 1 ≤ T ≤ W − 1 (p.33) → ws : List ℕ, T : ℕ with SSRange ws T; reason: the standing assumption of Appendix B.1.1 written as a hypothesis
--   - reading: λ (the lemma's payment vector) → λ ∈ ℝ²₊, i.e. 0 ≤ λ₁, 0 ≤ λ₂; reason: p.33: the reduction uses payment vectors λ = (λ₁, λ₂) ∈ ℝ²₊
--   - encoding: items i ∈ [k] = {1, …, k} → i : Fin k, item i of Lean is item i + 1 of the paper (3^{−i} is tern i = 3^{−(i+1)}); reason: Lean convention; same instances
--   - encoding: real edge weights and costs → rationals cast to ℝ; reason: every number of the construction is rational; same instance
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Lemma B.3, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_CritContracts_Construction

set_option autoImplicit false

namespace CritContracts

open Construction

/-- **Lemma B.3** (Ezra–Feldman–Molina–Schlesinger, *Sources of Complexity in Multi-Agent Combinatorial Contracts*,
STOC 2027 submission (manuscript sha256 430be35c…), Appendix B.1.1, p.35, PDF p.36): for all `i ∈ [k]`, if `q_i ∈ S(λ)`
then `λ₁ ≥ 1/2 − 4Δ`, and if `p_i ∈ S(λ)` then `λ₂ ≥ 1/2 − 4Δ`.

**Formalization Note** The Subset Sum instance has positive integer weights \`ws = [w₁, …, w_k]\` and target \`T\` with
\`k ≥ 1\` and \`1 ≤ T ≤ W − 1\` (the "without loss of generality" of p.33, \`SSRange\`). `S(λ)` is `(auxInst ws T).stableUnion λ` for `λ ∈ ℝ²₊` (no bound on
`λ₁ + λ₂`, as on the page). `λ₁ = lam 0` (agent 1, side `U`), `λ₂ = lam 1`. Items are \`0, …, k − 1\` here and \`1, …, k\` in the paper. -/
theorem lemma_B_3 (ws : List ℕ) (T : ℕ) (hWLOG : SSRange ws T)
    (lam : Fin 2 → ℝ) (hlam : ∀ s, 0 ≤ lam s) (i : Fin ws.length) :
    (Node.q i ∈ (auxInst ws T).stableUnion lam → 1 / 2 - 4 * (Delta ws : ℝ) ≤ lam 0) ∧
    (Node.p i ∈ (auxInst ws T).stableUnion lam → 1 / 2 - 4 * (Delta ws : ℝ) ≤ lam 1) := by sorry

end CritContracts
