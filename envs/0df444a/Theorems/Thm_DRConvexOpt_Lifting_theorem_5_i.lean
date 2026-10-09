-- Prove2me | Theorems.Thm_DRConvexOpt_Lifting_theorem_5_i
-- name    : DRConvexOpt.Lifting.theorem_5_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:32:59.468918+00:00
-- url     : https://prove2.me/theorems/ea51db4e-59f9-4019-a165-a7a83e77542d
-- title:
--   Theorem 5 (i) (Lifting Theorem), p. 15 — 𝒫′ = Π_z̃𝒫
-- statement:
--   Let $f \in \mathbb R^M$, let $g : \mathbb R^P \to \mathbb R^M$ be measurable, let $\mathcal K \subseteq \mathbb R^M$ be a proper cone, and let $\mathcal C_i \subseteq \mathbb R^P$, $i \in \mathcal I$, be measurable sets with bounds $\underline p_i, \overline p_i \in \mathbb R$. Consider the ambiguity set
--   $$
--   \mathcal P' = \Big\{ \mathbb Q \in \mathcal P_0(\mathbb R^P) : \ \mathbb E_{\mathbb Q}[g(\tilde z)] \preccurlyeq_{\mathcal K} f,\ \ \mathbb Q[\tilde z \in \mathcal C_i] \in [\underline p_i, \overline p_i]\ \ \forall i \in \mathcal I \Big\}
--   $$
--   and the lifted ambiguity set, involving an auxiliary random vector $\tilde u \in \mathbb R^M$,
--   $$
--   \mathcal P = \Big\{ \mathbb P \in \mathcal P_0(\mathbb R^P \times \mathbb R^M) : \ \mathbb E_{\mathbb P}[\tilde u] = f,\ \ \mathbb P[g(\tilde z) \preccurlyeq_{\mathcal K} \tilde u] = 1,\ \ \mathbb P[\tilde z \in \mathcal C_i] \in [\underline p_i, \overline p_i]\ \ \forall i \in \mathcal I \Big\}.
--   $$
--   Then
--   $$
--   \mathcal P' = \Pi_{\tilde z}\mathcal P .
--   $$
--
--   The theorem says that a conic bound on a (possibly nonlinear) moment $\mathbb E[g(\tilde z)]$ can be traded for a linear expectation constraint on an auxiliary vector plus an almost-sure conic constraint, without changing the set of distributions of $\tilde z$. This is how the paper fits higher-order moment information into its standardized ambiguity set.
--
--   **Formalization Note** Only assertion (i) is formalized; assertion (ii), that $\mathcal P$ "can be reformulated as an instance of the standardized ambiguity set (4)", rests on the informal notion of a conic representable epigraph. The page's hypothesis that $g$ has a conic representable $\mathcal K$-epigraph is not used by (i) and is dropped (a strengthening); $g$ is only assumed measurable, which $\mathbb E[g(\tilde z)]$ presupposes. Every expectation is read as existing and finite: $\mathcal P'$ requires $g(\tilde z)$ integrable, and $\mathcal P$ requires $\tilde u$ and $g(\tilde z)$ integrable. The last clause is an addition to the page and is necessary: with $M = 1$, $\mathcal K = \mathbb R_+$, $f = 0$, $g(z) = -z^2$, $\tilde z$ standard Cauchy and $\tilde u \equiv 0$, the joint law satisfies the page's constraints but $\mathbb E[g(\tilde z)]$ does not exist. The confidence sets are arbitrary measurable subsets of $\mathbb R^P$ (the paper's conic sets (5) are closed, hence a special case). The index set $\mathcal I$ is `Fin nI`.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 15, Theorem 5 (i); proof p. 40

import Mathlib
import Definitions.Def_DRConvexOpt_Lifting_Setting

namespace DRConvexOpt.Lifting

open MeasureTheory

/-- Theorem 5 (i) (Lifting Theorem), p. 15: 𝒫′ = Π_z̃𝒫. -/
theorem theorem_5_i {nP nM nI : ℕ} (g : (Fin nP → ℝ) → (Fin nM → ℝ)) (hg : Measurable g)
    (f : Fin nM → ℝ) (K : Set (Fin nM → ℝ)) (hK : DRConvexOpt.Reform.IsProperCone K)
    (C : Fin nI → Set (Fin nP → ℝ)) (hC : ∀ i, MeasurableSet (C i)) (plo phi : Fin nI → ℝ) :
    momentSet g f K C plo phi = marginal (liftedSet g f K C plo phi) := by sorry

end DRConvexOpt.Lifting
