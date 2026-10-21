-- Prove2me | Theorems.Thm_ConstrInfoDesign_Cav_proposition_A_2
-- name    : ConstrInfoDesign.Cav.proposition_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:26.198411+00:00
-- url     : https://prove2.me/theorems/8c7a1f39-a82a-4daa-88ce-c50b196f17b1
-- title:
--   Proposition A.2, p. 25 — cav h(x) is the supremum of ∑ λm h(xm) over at most D + 1 points of dom h with mean x (Rockafellar, Cor. 17.1.5)
-- statement:
--   Let $h$ be a function on a $D$-dimensional real vector space with values in $[-\infty, +\infty)$, and let $\operatorname{dom} h = \{x : h(x) > -\infty\}$. Then for every $x$,
--   $$(\operatorname{cav} h)(x) = \sup\Big\{\sum_{m=1}^M \lambda_m h(x_m) : \{x_1, \dots, x_M\} \subseteq \operatorname{dom} h,\ \lambda \in \Delta_x(\{x_1, \dots, x_M\}),\ M \le D + 1\Big\},$$
--   where $\lambda \in \Delta_x(\{x_1, \dots, x_M\})$ means $\lambda_m \ge 0$, $\sum_m \lambda_m = 1$ and $\sum_m \lambda_m x_m = x$, and the supremum of the empty set is $-\infty$.
--
--   This representation of the concave hull (Definition 2.1) by finite convex combinations of at most $D+1$ points is what the proof of Theorem 3.1 uses to compare $\operatorname{cav} f^{\bar g}$ with finitely supported distributions over posteriors.
--
--   **Formalization Note** The paper writes $h : \mathbb R^D \to \mathbb R$ but applies the result to $f^{\bar g}$, which takes the value $-\infty$; the statement is therefore for extended-real-valued $h$ with $h < +\infty$ everywhere (as Assumption 1 gives for $f^{\bar g}$). $\mathbb R^D$ is any finite-dimensional real vector space, with $D$ its dimension (`Module.finrank`). The points $x_m$ are an indexed family, so repetitions are allowed; this does not change the supremum.
-- source:
--   Doval and Skreta, Constrained Information Design, arXiv:1811.03588v3, p. 25, Proposition A.2 (Rockafellar 1970, Corollary 17.1.5)

import Mathlib
import Definitions.Def_ConstrInfoDesign_Cav_Model

namespace ConstrInfoDesign.Cav

open MeasureTheory

/-- Proposition A.2 (Doval–Skreta, arXiv:1811.03588v3, p. 25; Rockafellar 1970, Corollary 17.1.5):
for `h : ℝ^D → [−∞, +∞)`, `(cav h)(x)` is the supremum of `∑ λ_m h(x_m)` over at most `D + 1`
points `x_m` of `dom h = {h > −∞}` and weights `λ ∈ Δ` with `∑ λ_m x_m = x`. Here `ℝ^D` is any
finite-dimensional real vector space and `D` its dimension. -/
theorem proposition_A_2 {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] (h : E → EReal) (hh : ∀ x, h x < ⊤) (x : E) : cav h x = sSup {v : EReal | ∃ (M : ℕ) (xs : Fin M → E) (w : Fin M → ℝ), M ≤ Module.finrank ℝ E + 1 ∧ (∀ m, h (xs m) ≠ ⊥) ∧ (∀ m, 0 ≤ w m) ∧ ∑ m, w m = 1 ∧ ∑ m, w m • xs m = x ∧ v = ((∑ m, w m * (h (xs m)).toReal : ℝ) : EReal)} := by sorry

end ConstrInfoDesign.Cav
