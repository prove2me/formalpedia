-- Prove2me | Theorems.Thm_BewleyGE_lemma_1
-- name    : BewleyGE.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:32:35.109978+00:00
-- url     : https://prove2.me/theorems/8d37b7aa-e072-45c7-b359-113f30a4f00b
-- title:
--   Lemma 1 — the savings policy is single-valued and continuous; the value function is continuous, increasing and strictly concave
-- statement:
--   Consider an economy whose utility satisfies Assumption 1. For all prices $p\gg0$ and interest rates $r\in(0,1)$ there exist a demand function $x^*(\cdot,p)$, a value function $V(\cdot,p,r)$ (the bounded fixed point of the Bellman operator on $A(p,r)$) and a savings policy $g(\cdot,p,r)$ satisfying (1), such that:
--
--   1. the value function is the unique bounded fixed point: any bounded $V'$ with $TV'=V'$ agrees with $V$ on $A(p,r)$;
--   2. $g$ is single-valued: for every $a\in A(p,r)$, $g(a,p,r)$ is the only maximizer in (1);
--   3. $a\mapsto V(a,p,r)$ is increasing and strictly concave on $A(p,r)$;
--   4. $g(a,p,r)$ and $V(a,p,r)$ are jointly continuous in $(a,p,r)$ on $\{(a,p,r): p\gg0,\ 0<r<1,\ a\in A(p,r)\}$.
--
--   The lemma makes the agents' problem well posed at every price and supplies the continuity in prices on which the continuity of the excess demand rests.
--
--   Differences from the source:
--   - generalization: the §2 model: 𝒴 = 𝒴₁ × ⋯ × 𝒴ₙ with a strict top element y′ (y′ − y ≫ 0 for all other y) → any finite set 𝒴 of strictly positive vectors with e > 0 summing to 1, no product form and no top element; reason: the statement does not use the endowment structure; it specializes to the paper's model
--   - reading: Assumption 1: U continuously differentiable with ∂U(0)/∂xⱼ = ∞; u_p continuously differentiable → U continuous on ℝⁿ₊ and C¹ on the open orthant, (U(t eⱼ) − U(0))/t → ∞ as t ↓ 0; u_p C¹ on (0, ∞); reason: C¹ on the closed orthant contradicts ∂U(0)/∂xⱼ = ∞ and excludes the paper's CES example; u_p′(0+) = ∞ excludes C¹ at 0
--   - reading: U strictly increasing: x > x′ implies U(x) > U(x′), with x > x′ undefined → x′ ≤ x coordinatewise and x′ ≠ x imply U(x′) < U(x); reason: the paper defines only x ≥ x′; the proof of Lemma 8 (p.27) uses this reading
--   - encoding: V(a) = sup over strategies of expected discounted utility (p.6) → V bounded on A(p, r) with TV = V and the maximum attained; reason: the paper's own characterization of V as the unique bounded fixed point of T (p.7, footnote 10)
--   - encoding: g(·, p, r) defined on A(p, r), with no regularity stated in (1) → the savings policy is a measurable function on ℝ (values off A(p, r) otherwise free); reason: the paper's g is continuous on the compact A(p, r) (Lemma 1), so it has measurable extensions, and the wealth operator only sees g on A(p, r); measurability keeps the image measures of (2) from being zero
--   - reading: continuity "on ℝ × ℝⁿ₊₊ × (0, 1)" → continuity on {(a, p, r) : p ≫ 0, 0 < r < 1, a ∈ A(p, r)}; reason: V and T live on B(A(p, r)) (p.7) and C(a, p) is empty for a < a̲(p, r); the state space moves with the prices, so continuity is joint on its graph
--   - generalization: the lemma presupposes that x*, V and g exist and that V is the unique fixed point of T (p.7) → these existence and uniqueness facts are part of the conclusion; reason: dropping them gives the printed lemma
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Lemma 1, p.21

import Mathlib
import Definitions.Def_BewleyGE_Assumption1
import Definitions.Def_BewleyGE_IsDemand
import Definitions.Def_BewleyGE_IsValueFunction
import Definitions.Def_BewleyGE_IsSavingsPolicy

namespace BewleyGE

/-- **Lemma 1 (savings policy and value function).** Light, arXiv:1906.06810v2, Lemma 1, p.21:
"The savings policy function g(a, p, r) is single-valued and continuous in (a, p, r) on
R × Rⁿ₊₊ × (0, 1). The value function V(a, p, r) is continuous in (a, p, r) on R × Rⁿ₊₊ × (0, 1),
increasing in a, and strictly concave in a."

Under Assumption 1 there are a demand function `x(·, p)`, a value function `V(·, p, r)` and a
savings policy `g(·, p, r)` for every `p ≫ 0`, `0 < r < 1`, such that the bounded fixed point `V`
is unique on `A(p, r)`, the maximizer in (1) is unique (`g` single-valued), `V` is increasing and
strictly concave on `A(p, r)`, and `g` and `V` are jointly continuous in `(a, p, r)` on the set
`{(a, p, r) : p ≫ 0, 0 < r < 1, a ∈ A(p, r)}`.

**Formalization Note.** The domain `ℝ × ℝⁿ₊₊ × (0, 1)` is read as the graph of `A(p, r)` (reading
R5): below `a̲(p, r)` the savings set `C(a, p)` is empty and `g` is undefined. Points are
`(a, p, r)` as `ℝ × (Fin n → ℝ) × ℝ`. Existence and uniqueness of the Bellman solution are stated
here because every later item depends on them. -/
theorem lemma_1 {n : ℕ} (E : Economy n) (hA : Assumption1 E) :
    ∃ (x : (Fin n → ℝ) → ℝ → Fin n → ℝ) (V g : (Fin n → ℝ) → ℝ → ℝ → ℝ),
      (∀ (p : Fin n → ℝ) (r : ℝ), (∀ i, 0 < p i) → 0 < r → r < 1 →
        IsDemand E p (x p) ∧ IsValueFunction E p r (x p) (V p r) ∧
        IsSavingsPolicy E p r (x p) (V p r) (g p r) ∧
        (∀ V' : ℝ → ℝ, IsValueFunction E p r (x p) V' →
          ∀ a ∈ wealthSet E p r, V' a = V p r a) ∧
        (∀ a ∈ wealthSet E p r, ∀ b ∈ savingsSet E p r a,
          bellmanObjective E p r (x p) (V p r) a b = V p r a → b = g p r a) ∧
        MonotoneOn (V p r) (wealthSet E p r) ∧
        StrictConcaveOn ℝ (wealthSet E p r) (V p r)) ∧
      ContinuousOn (fun z : ℝ × (Fin n → ℝ) × ℝ => g z.2.1 z.2.2 z.1)
        {z | (∀ i, 0 < z.2.1 i) ∧ 0 < z.2.2 ∧ z.2.2 < 1 ∧ z.1 ∈ wealthSet E z.2.1 z.2.2} ∧
      ContinuousOn (fun z : ℝ × (Fin n → ℝ) × ℝ => V z.2.1 z.2.2 z.1)
        {z | (∀ i, 0 < z.2.1 i) ∧ 0 < z.2.2 ∧ z.2.2 < 1 ∧ z.1 ∈ wealthSet E z.2.1 z.2.2} := by sorry

end BewleyGE
