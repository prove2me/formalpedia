-- Prove2me | Theorems.Thm_DPDeconstructed_theorem_3_2
-- name    : DPDeconstructed.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:49:08.252491+00:00
-- url     : https://prove2.me/theorems/8446b878-0054-4580-aa3a-b9816f4bc7dd
-- title:
--   Theorem 3.2 (corrected: $W_0$, $W_1$ monotone on $\mathcal V$, $\mathcal G$) — $g^*$ solves the refactored Bellman equation in $\mathbb G$ iff $v^*$ solves the Bellman equation in $\mathbb V$
-- statement:
--   Let a dynamic program satisfy Assumption 2.1 (for the set $\mathbb V$) and Assumption 2.2, let $(W_0,W_1)$ be a plan factorization, $\hat g:=W_0v^*$ (26) and $g^*(x,a)=\sup_{\sigma\in\Sigma}g_\sigma(x,a)$ (27). If $W_0$ is monotone on $\mathcal V$ and $W_1$ is monotone on $\mathcal G$, then the following are equivalent:
--
--   1. $g^*$ lies in $\mathbb G$ and satisfies the refactored Bellman equation $g^*=W_0MW_1g^*$;
--   2. $v^*$ lies in $\mathbb V$ and satisfies the Bellman equation $v^*=Tv^*$.
--
--   If these conditions hold, then $g^*=\hat g$, the set of optimal policies is nonempty, and for every $\sigma\in\Sigma$
--
--   $$\sigma\text{ is optimal}\iff\sigma\text{ is }g^*\text{-greedy}\iff\sigma\text{ is }v^*\text{-greedy}.\qquad(28)$$
--
--   The theorem shows that the standard and refactored Bellman equations have "equal rights": either can be solved to obtain the same optimal policies.
--
--   **Formalization Note** "If these conditions hold" is stated for every $g\in\mathbb G$ equal to $g^*$ with $Sg=g$ and every $w\in\mathbb V$ equal to $v^*$ with $Tw=w$; then $g^*=\hat g$ reads $g^*=W_0w$, and $g^*$-greedy means $g$-greedy.
--
--   Differences from the source:
--   - correction: W₀ and W₁ are monotone (p.14: with respect to the pointwise order on 𝕍, 𝔾 and ℍ) → W₀ is monotone on 𝒱 and W₁ is monotone on 𝒢 (MonotoneOn); reason: the printed domains make the statement false: X = {x}, Γ(x) = {a, b}, 𝒱 = ℝ, H(x,a,v) = v/2 + 1, H(x,b,v) = v/2, 𝕍 = {2}, W₀v = (−v, −v), W₁(g_a, g_b) = (−g_a/2 + 1, −g_b/2) satisfies every assumption, yet g* = (0, 0) ∉ 𝔾 while Tv* = v* = 2; the proof applies monotonicity at v_σ ∈ 𝒱 and g_σ ∈ 𝒢, the domains on which W₀ and W₁ are defined
--   - encoding: H valued in ℝ ∪ {−∞}; T v, M h, v* and g* are suprema (possibly infinite) → EReal values; "v* lies in 𝕍" and "g* lies in 𝔾" are the existence of a real w ∈ 𝕍 (resp. g ∈ 𝔾) equal to v* (resp. g*) as EReal-valued functions; reason: Lean convention for extended-real suprema; same instances
--   - encoding: If these conditions hold, then g* = ĝ, … (28) → for every g ∈ 𝔾 equal to g* with S g = g and every w ∈ 𝕍 equal to v* with T w = w: g* = W₀ w, an optimal policy exists, and optimal ⟺ g-greedy ⟺ v*-greedy for every σ; reason: under either condition such g and w exist (the first part) and equal g*, v*; ĝ = W₀v* is W₀w
--   - encoding: S = W₀ M W₁ defined on 𝔾 → S g = W₀ (toReal ∘ M W₁ g), a total map applied only to elements of 𝔾; reason: on 𝔾, M W₁ g = T v is a real element of 𝕍, so S agrees with the paper's operator there; its values off 𝔾 never enter the statement
--   - encoding: plan factorization: W₀ defined on 𝒱 with values in 𝒢, W₁ defined on 𝒢 with values in ℋ, and (7) → structure with total maps W₀ on ℝ^X, W₁ on ℝ^F and the single field (7); reason: 𝒢 := W₀𝒱 gives the first condition and (7) gives the second; values off 𝒱 and 𝒢 never enter a statement, so every pair on the page is an instance
--   - encoding: 𝕍 is the set whose existence Assumption 2.1 asserts → 𝕍 is a parameter with the hypothesis Assumption21 𝕍; reason: the statement holds for each such set, which covers the one the paper fixes; 𝔾 and the domain of S depend on it
-- source:
--   Ma and Stachurski, Dynamic Programming Deconstructed: Transformations of the Bellman Equation and Computational Efficiency, arXiv:1811.01940v2, §3.1, p.14, Theorem 3.2 (with (26), (27), p.13, and the monotonicity and g-greedy definitions of p.14)

import Mathlib
import Definitions.Def_DPDeconstructed_PlanFactorization

namespace DPDeconstructed

open DynProg PlanFactorization

/-- Theorem 3.2, Ma and Stachurski, *Dynamic Programming Deconstructed*, arXiv:1811.01940v2,
§3.1, p.14. Let a dynamic program satisfy Assumption 2.1 (for the set `𝕍`) and Assumption 2.2,
let `(W₀, W₁)` be a plan factorization, let `ĝ := W₀ v*` (26) and let `g*` be the refactored
value function (27). If `W₀` and `W₁` are both monotone, then the following are equivalent:
(1) `g*` lies in `𝔾` and satisfies the refactored Bellman equation (10), `g* = W₀ M W₁ g*`;
(2) `v*` lies in `𝕍` and satisfies the Bellman equation (1), `v* = T v*`.
If these conditions hold, then `g* = ĝ`, the set of optimal policies is nonempty and, for
`σ ∈ Σ`, (28): `σ` is optimal ⟺ `σ` is `g*`-greedy ⟺ `σ` is `v*`-greedy.

**Formalization Note** (Correction.) p.14 takes monotonicity "with respect to the pointwise
partial order on `𝕍`, `𝔾` and `ℍ`"; here it is on the domains of definition of the operators:
`W₀` on `𝒱` and `W₁` on `𝒢`. With monotonicity only on `𝕍` and `𝔾` the theorem is
false (one state, actions `a, b`, `𝒱 = ℝ`, `H(x,a,v) = v/2 + 1`, `H(x,b,v) = v/2`, `𝕍 = {2}`,
`W₀ v = (−v, −v)`, `W₁(g_a, g_b) = (−g_a/2 + 1, −g_b/2)`: then `g* = (0, 0) ∉ 𝔾` while
`T v* = v*`). "`g*` lies in `𝔾`" means some `g ∈ 𝔾` equals `g*` as `EReal`-valued functions, and
likewise for `v* ∈ 𝕍`. The consequences are stated for any such `g` and `w`, both of which exist
under either condition; `g* = ĝ` is `g* = W₀ w` with `w` the real function equal to `v*`, and
"`g*`-greedy" is `g`-greedy. -/
theorem theorem_3_2 {X A : Type*} [Nonempty X] (D : DynProg X A) (𝕍 : Set (X → ℝ))
    (h21 : D.Assumption21 𝕍) (h22 : D.Assumption22) (P : PlanFactorization D)
    (hW₀ : MonotoneOn P.W₀ D.𝒱) (hW₁ : MonotoneOn P.W₁ P.calG) :
    ((∃ g ∈ P.bbG 𝕍, (∀ p, (g p : EReal) = P.gstar p) ∧ P.S g = g) ↔
        ∃ w ∈ 𝕍, (∀ x, (w x : EReal) = D.vstar x) ∧ ∀ x, D.T w x = (w x : EReal)) ∧
      ∀ g ∈ P.bbG 𝕍, (∀ p, (g p : EReal) = P.gstar p) → P.S g = g →
        ∀ w ∈ 𝕍, (∀ x, (w x : EReal) = D.vstar x) → (∀ x, D.T w x = (w x : EReal)) →
          (∀ p, P.gstar p = (P.W₀ w p : EReal)) ∧ (∃ σ : D.Policy, D.IsOptimal σ) ∧
            ∀ σ : D.Policy,
              (D.IsOptimal σ ↔ P.IsGGreedy g σ) ∧ (P.IsGGreedy g σ ↔ D.IsVStarGreedy σ) := by sorry

end DPDeconstructed
