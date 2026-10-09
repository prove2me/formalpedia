-- Prove2me | Theorems.Thm_ExtraConsensus_Sublinear_proposition_2_1
-- name    : ExtraConsensus.Sublinear.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:42.325228+00:00
-- url     : https://prove2.me/theorems/8eb91065-503f-42ee-9866-15ad909c20a8
-- title:
--   Proposition 2.1, p. 5 — if null{I − W} = span{1}, x* = Wx* and 1ᵀ∇f(x*) = 0, every row of x* solves (1.1)
-- statement:
--   Let $W\in\mathbb R^{n\times n}$ satisfy $\operatorname{null}\{I-W\}=\operatorname{span}\{\mathbf 1\}$, and let $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ be convex and differentiable. Suppose the stacked variable $\mathbf x^*\in\mathbb R^{n\times p}$, with rows $x^*_{(1)},\dots,x^*_{(n)}$, satisfies
--
--   1. $\mathbf x^*=W\mathbf x^*$ (consensus),
--   2. $\mathbf 1^{\mathsf T}\nabla\mathbf f(\mathbf x^*)=\sum_{i=1}^n\nabla f_i(x^*_{(i)})=0$ (optimality).
--
--   Then all rows coincide, $x^*_{(1)}=\dots=x^*_{(n)}$, and each row is a solution of the consensus problem (1.1):
--   $$\bar f(x^*_{(i)})\le\bar f(y)\quad\text{for all }y\in\mathbb R^p\text{ and all }i,\qquad \bar f=\tfrac1n\textstyle\sum_{j}f_j.$$
--
--   The two conditions are the targets EXTRA is constructed to reach at its limit.
--
--   **Formalization Note** The page's standing convexity and differentiability of the $f_i$ (§1) are hypotheses. The conclusion "$x^*=x^*_{(i)}$, for any $i$, is a solution" is stated as two clauses: the rows coincide, and each row minimizes $\bar f$.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, Proposition 2.1, p. 5

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace ExtraConsensus.Sublinear

open Matrix Filter Topology Asymptotics

/-- Proposition 2.1, p. 5. Assume `null{I − W} = span{𝟏}` and that every `fᵢ` is convex and
differentiable. If `𝐱*` satisfies `𝐱* = W𝐱*` (consensus) and `𝟏ᵀ∇𝐟(𝐱*) = 0` (optimality), then all
rows of `𝐱*` coincide and each row `x*₍ᵢ₎` solves problem (1.1). -/
theorem proposition_2_1 {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (hnull : ∀ v : Fin n → ℝ, (1 - W) *ᵥ v = 0 ↔ ∃ c : ℝ, v = fun _ => c)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hdiff : ∀ i, Differentiable ℝ (f i))
    (xs : Stack n p) (hcons : mix W xs = xs) (hopt : ∑ i, gradient (f i) (xs i) = 0) :
    (∀ i j, xs i = xs j) ∧ ∀ i, ∀ y, fbar f (xs i) ≤ fbar f y := by sorry

end ExtraConsensus.Sublinear
