-- Prove2me | Theorems.Thm_DPDeconstructed_theorem_3_3_refactored_optimality
-- name    : DPDeconstructed.theorem_3_3_refactored_optimality
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:48:43.847668+00:00
-- url     : https://prove2.me/theorems/5cb8b0f3-c9e4-4232-80c2-c4201071e07e
-- title:
--   Theorem 3.3 (corrected: $W_0$, $W_1$ monotone on $\mathcal V$, $\mathcal G$) — refactored value iteration converges to $g^*$, and $g^*$-greedy policies are optimal
-- statement:
--   Let a dynamic program satisfy Assumption 2.1 (for the set $\mathbb V$) and Assumption 2.2, let $(W_0,W_1)$ be a plan factorization with refactored Bellman operator $S=W_0MW_1$ on $\mathbb G$, refactored $\sigma$-value operators $S_\sigma=W_0M_\sigma W_1$ on $\mathcal G$ and refactored value function $g^*=\sup_{\sigma\in\Sigma}g_\sigma$, and let $\tau$ be a Hausdorff topology on $\mathcal G$ under which the pointwise partial order is closed. Suppose that
--
--   1. $W_0$ is monotone on $\mathcal V$ and $W_1$ is monotone on $\mathcal G$,
--   2. $S$ is asymptotically stable on $\mathbb G$, and
--   3. every $S_\sigma$, $\sigma\in\Sigma$, is asymptotically stable on $\mathcal G$.
--
--   Then
--
--   1. $g^*$ is the unique solution in $\mathbb G$ of the refactored Bellman equation $g=W_0MW_1g$;
--   2. $\displaystyle\lim_{k\to\infty}S^kg=g^*$ under $\tau$ for every $g\in\mathbb G$;
--   3. at least one optimal policy exists; and
--   4. a feasible policy is optimal if and only if it is $g^*$-greedy.
--
--   The theorem justifies computing with the refactored operator, often on a lower-dimensional space: refactored value iteration converges to $g^*$, and a $g^*$-greedy policy is optimal.
--
--   **Formalization Note** $\tau$ is a topology on the subtype $\mathcal G$, $\mathbb G$ carries the subspace topology, and convergence is stated in $(\mathcal G,\tau)$. $g^*$ is extended-real valued: conclusion 1 asserts a $g\in\mathbb G$ that equals $g^*$ pointwise, is a fixed point of $S$, and is the only fixed point of $S$ in $\mathbb G$; conclusions 2 and 4 refer to that $g$.
--
--   Differences from the source:
--   - correction: W₀ and W₁ are monotone (p.14: with respect to the pointwise order on 𝕍, 𝔾 and ℍ) → W₀ is monotone on 𝒱 and W₁ is monotone on 𝒢 (MonotoneOn); reason: the printed domains make the statement false: X = {x}, Γ(x) = {a, b}, 𝒱 = ℝ, H(x,a,v) = v/2 + 1, H(x,b,v) = v/2, 𝕍 = {2}, W₀v = (−v, −v), W₁(g_a, g_b) = (−g_a/2 + 1, −g_b/2) satisfies every assumption, yet g* = (0, 0) ∉ 𝔾 while Tv* = v* = 2; the proof applies monotonicity at v_σ ∈ 𝒱 and g_σ ∈ 𝒢, the domains on which W₀ and W₁ are defined
--   - encoding: Hausdorff topology τ on 𝒢; asymptotic stability on 𝔾 with respect to τ → τ : TopologicalSpace ↥𝒢; convergence of sequences of 𝔾 stated in (↥𝒢, τ); reason: 𝔾 ⊆ 𝒢 has the subspace topology, and for sequences and limits in 𝔾 subspace convergence equals convergence in (𝒢, τ)
--   - encoding: g* is the unique solution of (10) in 𝔾 (g* extended-real) → some g ∈ 𝔾 equals g* in EReal, S g = g, and every fixed point of S in 𝔾 equals g; (2) and (4) are stated for that g; reason: Lean convention for the extended-real supremum g*; same instances
--   - encoding: S = W₀ M W₁ defined on 𝔾 → S g = W₀ (toReal ∘ M W₁ g), a total map applied only to elements of 𝔾; reason: on 𝔾, M W₁ g = T v is a real element of 𝕍, so S agrees with the paper's operator there; its values off 𝔾 never enter the statement
--   - encoding: plan factorization: W₀ defined on 𝒱 with values in 𝒢, W₁ defined on 𝒢 with values in ℋ, and (7) → structure with total maps W₀ on ℝ^X, W₁ on ℝ^F and the single field (7); reason: 𝒢 := W₀𝒱 gives the first condition and (7) gives the second; values off 𝒱 and 𝒢 never enter a statement, so every pair on the page is an instance
--   - encoding: 𝕍 is the set whose existence Assumption 2.1 asserts → 𝕍 is a parameter with the hypothesis Assumption21 𝕍; reason: the statement holds for each such set, which covers the one the paper fixes; 𝔾 and the domain of S depend on it
--   - encoding: self-mapping A on U, asymptotically stable on U → AsympStableOn τ A U for a total map A: MapsTo U U, a unique fixed point in U, convergence through TendstoIn; reason: S maps 𝔾 into 𝔾 and S_σ maps 𝒢 into 𝒢 on every instance (Assumption 2.1, (4), (7)), so MapsTo excludes nothing
-- source:
--   Ma and Stachurski, Dynamic Programming Deconstructed: Transformations of the Bellman Equation and Computational Efficiency, arXiv:1811.01940v2, §3.2, p.15, Theorem 3.3 (standing topology τ and asymptotic stability, p.15; Assumptions 2.1–2.2, pp.5–6)

import Mathlib
import Definitions.Def_DPDeconstructed_PlanFactorization
import Definitions.Def_DPDeconstructed_AsympStable

namespace DPDeconstructed

open DynProg PlanFactorization

/-- Theorem 3.3, Ma and Stachurski, *Dynamic Programming Deconstructed*, arXiv:1811.01940v2,
§3.2, p.15. Let a dynamic program (§2.1) satisfy Assumption 2.1 (for the set `𝕍`) and
Assumption 2.2, let `(W₀, W₁)` be a plan factorization with refactored Bellman operator
`S = W₀ M W₁` on `𝔾`, refactored `σ`-value operators `S_σ = W₀ M_σ W₁` on `𝒢` and refactored
value function `g*` (27), and let `τ` be a Hausdorff topology on `𝒢` under which the pointwise
partial order is closed (p.15). If `W₀` and `W₁` are monotone, `S` is asymptotically stable on
`𝔾` and `{S_σ}_{σ ∈ Σ}` are asymptotically stable on `𝒢`, then
(1) `g*` is the unique solution to the refactored Bellman equation in `𝔾`,
(2) `lim_{k → ∞} S^k g = g*` under `τ` for all `g ∈ 𝔾`,
(3) at least one optimal policy exists, and
(4) a feasible policy is optimal if and only if it is `g*`-greedy.

**Formalization Note** (Correction.) p.14 takes monotonicity "with respect to the pointwise
partial order on `𝕍`, `𝔾` and `ℍ`"; here "monotone" is `MonotoneOn W₀ 𝒱` and
`MonotoneOn W₁ 𝒢`, the domains of definition of the operators. With monotonicity only on `𝕍`
and `𝔾` the theorem is false (one
state, actions `a, b`, `𝒱 = ℝ`, `H(x,a,v) = v/2 + 1`, `H(x,b,v) = v/2`, `𝕍 = {2}`,
`W₀ v = (−v, −v)`, `W₁(g_a, g_b) = (−g_a/2 + 1, −g_b/2)`, where `g* = (0, 0) ∉ 𝔾`). `τ` is a
topology on the subtype `↥𝒢`; `𝔾 ⊆ 𝒢` carries the subspace topology, and convergence is stated
in `(↥𝒢, τ)` (`TendstoIn`). `g*` is `EReal`-valued: (1) says some `g ∈ 𝔾` equals `g*`, is a
fixed point of `S`, and is the only fixed point of `S` in `𝔾`; (2) and (4) refer to that `g`. -/
theorem theorem_3_3_refactored_optimality {X A : Type*} [Nonempty X] (D : DynProg X A)
    (𝕍 : Set (X → ℝ)) (h21 : D.Assumption21 𝕍) (h22 : D.Assumption22)
    (P : PlanFactorization D) (τ : TopologicalSpace P.calG) (hτ : IsHausdorffOrderClosed τ)
    (hW₀ : MonotoneOn P.W₀ D.𝒱) (hW₁ : MonotoneOn P.W₁ P.calG)
    (hS : AsympStableOn τ P.S (P.bbG 𝕍))
    (hSσ : ∀ σ : D.Policy, AsympStableOn τ (P.Sσ σ) P.calG) :
    ∃ g ∈ P.bbG 𝕍, (∀ p, (g p : EReal) = P.gstar p) ∧ P.S g = g ∧
      (∀ g' ∈ P.bbG 𝕍, P.S g' = g' → g' = g) ∧
      (∀ h ∈ P.bbG 𝕍, TendstoIn τ (fun k => P.S^[k] h) g) ∧
      (∃ σ : D.Policy, D.IsOptimal σ) ∧
      ∀ σ : D.Policy, D.IsOptimal σ ↔ P.IsGGreedy g σ := by sorry

end DPDeconstructed
