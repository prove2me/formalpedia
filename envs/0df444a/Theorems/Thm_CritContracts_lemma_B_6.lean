-- Prove2me | Theorems.Thm_CritContracts_lemma_B_6
-- name    : CritContracts.lemma_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:11.179979+00:00
-- url     : https://prove2.me/theorems/eb929135-4def-4a12-834e-8d83f177e32b
-- title:
--   Lemma B.6 (Amplification) — $r_0,r_1$ active activate $a,b$ and reward $\ge D$; otherwise reward $\le B$
-- statement:
--   Let $B$ be the total pre-amplification edge weight and $D=8\cdot3^kB/\varepsilon$, and let $f$ be the reward (2) of the auxiliary instance.
--
--   1. For $x\in[\tfrac12+\Delta L/4,\ \tfrac12+\Delta]$, if $r_0,r_1\in S(x,1-x)$, then $a,b\in S(x,1-x)$, and in particular $f(S(x,1-x))\ge D$.
--   2. For $\lambda\in\mathbb R^2_+$ with $\lambda_1+\lambda_2\le1+\varepsilon$, if at least one of $r_0,r_1$ is absent from $S(\lambda)$, then neither $a$ nor $b$ belongs to $S(\lambda)$, and $f(S(\lambda))\le B$.
--
--   The amplification edge $ab$ of weight $D$ turns successful verification into a reward far above everything else in the graph.
--
--
--   **Formalization Note** The Subset Sum instance is a list `ws` of positive weights with target `T`, $k\ge1$ and $1\le T\le W-1$; $S(\lambda)$ is the union of the $\lambda$-stable profiles of the auxiliary instance (`auxInst ws T`). Items are $0,\dots,k-1$ in Lean and $1,\dots,k$ in the paper. $r_0,r_1,a,b$ are `ver 0`, `ver 1`, `amp 0`, `amp 1`.
--
--   Differences from the source:
--
--   - encoding: a Subset Sum instance with positive integer weights w₁, …, w_k and target T, assumed WLOG to have k ≥ 1 and 1 ≤ T ≤ W − 1 (p.33) → ws : List ℕ, T : ℕ with SSRange ws T; reason: the standing assumption of Appendix B.1.1 written as a hypothesis
--   - reading: λ (the lemma's payment vector) → λ ∈ ℝ²₊, i.e. 0 ≤ λ₁, 0 ≤ λ₂; reason: p.33: the reduction uses payment vectors λ = (λ₁, λ₂) ∈ ℝ²₊
--   - encoding: real edge weights and costs → rationals cast to ℝ; reason: every number of the construction is rational; same instance
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Lemma B.6, p.36 (PDF p.37); B and D, p.36

import Mathlib
import Definitions.Def_CritContracts_Construction

set_option autoImplicit false

namespace CritContracts

open Construction

/-- **Lemma B.6 (Amplification)** (Ezra–Feldman–Molina–Schlesinger, *Sources of Complexity in Multi-Agent Combinatorial Contracts*,
STOC 2027 submission (manuscript sha256 430be35c…), Appendix B.1.1, p.36, PDF p.37): for
`x ∈ [1/2 + ΔL/4, 1/2 + Δ]`, if `r₀, r₁ ∈ S(x, 1 − x)`, then `a, b ∈ S(x, 1 − x)`, and in particular
`f(S(x, 1 − x)) ≥ D`. For `λ₁ + λ₂ ≤ 1 + ε`, if at least one of `(r₀, r₁)` is absent from `S(λ)`,
then neither `a` nor `b` belongs to `S(λ)`, and `f(S(λ)) ≤ B`.

**Formalization Note** The Subset Sum instance has positive integer weights \`ws = [w₁, …, w_k]\` and target \`T\` with
\`k ≥ 1\` and \`1 ≤ T ≤ W − 1\` (the "without loss of generality" of p.33, \`SSRange\`). `f` is the reward (2) of the auxiliary (unscaled, ungated) instance,
`B` the total pre-amplification edge weight and `D = 8·3^k·B/ε` (p.36). In the second part
`λ ∈ ℝ²₊`. `r₀ = ver 0`, `r₁ = ver 1`, `a = amp 0`, `b = amp 1`. -/
theorem lemma_B_6 (ws : List ℕ) (T : ℕ) (hWLOG : SSRange ws T) :
    (∀ x : ℝ, ((1 / 2 + Delta ws * Lpar ws / 4 : ℚ) : ℝ) ≤ x → x ≤ ((1 / 2 + Delta ws : ℚ) : ℝ) →
        Node.ver 0 ∈ (auxInst ws T).stableUnion (linePay x) →
        Node.ver 1 ∈ (auxInst ws T).stableUnion (linePay x) →
        Node.amp 0 ∈ (auxInst ws T).stableUnion (linePay x) ∧
          Node.amp 1 ∈ (auxInst ws T).stableUnion (linePay x) ∧
          (Dpar ws T : ℝ) ≤ (auxInst ws T).reward ((auxInst ws T).stableUnion (linePay x))) ∧
    (∀ lam : Fin 2 → ℝ, (∀ s, 0 ≤ lam s) → lam 0 + lam 1 ≤ 1 + (epsPar ws : ℝ) →
        (Node.ver 0 ∉ (auxInst ws T).stableUnion lam ∨ Node.ver 1 ∉ (auxInst ws T).stableUnion lam) →
        Node.amp 0 ∉ (auxInst ws T).stableUnion lam ∧ Node.amp 1 ∉ (auxInst ws T).stableUnion lam ∧
          (auxInst ws T).reward ((auxInst ws T).stableUnion lam) ≤ (Bpar ws T : ℝ)) := by sorry

end CritContracts
