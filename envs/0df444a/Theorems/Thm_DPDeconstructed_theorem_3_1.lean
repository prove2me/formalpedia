-- Prove2me | Theorems.Thm_DPDeconstructed_theorem_3_1
-- name    : DPDeconstructed.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:48:02.96735+00:00
-- url     : https://prove2.me/theorems/f136fca0-1479-488a-9c0a-8c7b1a03f1b5
-- title:
--   Theorem 3.1 — $v^*$ solves the Bellman equation in $\mathbb V$ iff the principle of optimality holds and an optimal policy exists
-- statement:
--   Let a dynamic program satisfy Assumption 2.2. The following are equivalent:
--
--   1. there is a set $\mathbb V\subseteq\mathcal V$ satisfying Assumption 2.1 ($T$ maps $\mathbb V$ into itself and a $v$-greedy policy exists for each $v\in\mathbb V$) such that the value function $v^*$ lies in $\mathbb V$ and satisfies the Bellman equation $v^*=Tv^*$;
--   2. Bellman's principle of optimality holds,
--
--   $$\sigma\text{ is optimal}\iff\sigma\text{ is }v^*\text{-greedy}\qquad(\sigma\in\Sigma),$$
--
--   and the set of optimal policies is nonempty.
--
--   This links the Bellman equation to optimal policies; Theorem 3.2 uses the direction (1) ⇒ (2).
--
--   **Formalization Note** $v^*$ and $T$ are extended-real valued; "$v^*$ lies in $\mathbb V$" means that some $w\in\mathbb V$ equals $v^*$ pointwise, and "$\sigma$ is $v^*$-greedy" includes that $v^*$ is a real element of $\mathcal V$.
--
--   Differences from the source:
--   - reading: (1) v* lies in 𝕍, the set of Assumption 2.1 → (1) v* lies in some 𝕍 ⊆ 𝒱 satisfying Assumption 2.1; reason: Assumption 2.1 begins "There exists a subset 𝕍"; for a fixed 𝕍 the direction (2) ⇒ (1) is false: X = {x}, Γ(x) = {a}, 𝒱 = ℝ, H(x,a,v) = v/2 and 𝕍 = ∅ satisfy Assumptions 2.1–2.2 and (2), but v* = 0 ∉ 𝕍
--   - encoding: standing Assumption 2.1 (there exists 𝕍 …) → not a separate hypothesis; reason: under the reading it is an existential statement that 𝕍 = ∅ always satisfies, so no instance changes
--   - encoding: σ is v*-greedy → v* equals some w ∈ 𝒱 as EReal functions and σ is w-greedy; reason: v-greedy (5) is defined for v ∈ 𝒱 while v* is a priori an extended-real function
--   - encoding: v* lies in 𝕍 and v* = Tv*; v* and T extended-real → some w ∈ 𝕍 equals v* in EReal and T w = w; reason: Lean convention for extended-real suprema; same instances
-- source:
--   Ma and Stachurski, Dynamic Programming Deconstructed: Transformations of the Bellman Equation and Computational Efficiency, arXiv:1811.01940v2, §3.1, p.13, Theorem 3.1 (Assumptions of §2.2 in force; definitions (24), (25), p.13)

import Mathlib
import Definitions.Def_DPDeconstructed_Policy

namespace DPDeconstructed

open DynProg

/-- Theorem 3.1, Ma and Stachurski, *Dynamic Programming Deconstructed*, arXiv:1811.01940v2,
§3.1, p.13, under Assumption 2.2 (standing, p.13). The next two statements are equivalent:
(1) the value function `v*` lies in `𝕍` and satisfies the Bellman equation (1), for some set
`𝕍 ⊆ 𝒱` satisfying Assumption 2.1;
(2) Bellman's principle of optimality (25) holds (for every `σ ∈ Σ`, `σ` is optimal iff `σ` is
`v*`-greedy) and the set of optimal policies is nonempty.

**Formalization Note** (Reading.) `𝕍` in (1) is existentially quantified over the subsets of
`𝒱` satisfying Assumption 2.1, as Assumption 2.1 itself begins "There exists a subset `𝕍` of
`𝒱`". For one fixed `𝕍` the direction (2) ⇒ (1) is false (one state, one action, `𝒱 = ℝ`,
`H(x, a, v) = v/2`, `𝕍 = ∅`). Since `𝕍 = ∅` satisfies Assumption 2.1, the standing Assumption
2.1 is not a separate hypothesis. "`v*` lies in `𝕍`" means some `w ∈ 𝕍` has `w = v*` as
`EReal`-valued functions, and "`σ` is `v*`-greedy" includes that `v*` is a real-valued element
of `𝒱` (`DynProg.IsVStarGreedy`). -/
theorem theorem_3_1 {X A : Type*} [Nonempty X] (D : DynProg X A) (h22 : D.Assumption22) :
    (∃ 𝕍 : Set (X → ℝ), D.Assumption21 𝕍 ∧
        ∃ w ∈ 𝕍, (∀ x, (w x : EReal) = D.vstar x) ∧ ∀ x, D.T w x = (w x : EReal)) ↔
      ((∀ σ : D.Policy, D.IsOptimal σ ↔ D.IsVStarGreedy σ) ∧ ∃ σ : D.Policy, D.IsOptimal σ) := by sorry

end DPDeconstructed
