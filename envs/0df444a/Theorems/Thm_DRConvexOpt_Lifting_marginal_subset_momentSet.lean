-- Prove2me | Theorems.Thm_DRConvexOpt_Lifting_marginal_subset_momentSet
-- name    : DRConvexOpt.Lifting.marginal_subset_momentSet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:32:04.070354+00:00
-- url     : https://prove2.me/theorems/940b5331-4b63-46c7-a346-454fe2a03e48
-- title:
--   Proof of Theorem 5, p. 40 — the z̃-marginal of every lifted distribution lies in 𝒫′
-- statement:
--   Let $g : \mathbb R^P \to \mathbb R^M$ be measurable, $f \in \mathbb R^M$, $\mathcal K \subseteq \mathbb R^M$ a proper cone, and $\mathcal C_i \subseteq \mathbb R^P$, $i \in \mathcal I$, measurable sets with bounds $\underline p_i, \overline p_i$. Then
--   $$
--   \Pi_{\tilde z}\mathcal P \subseteq \mathcal P',
--   $$
--   where $\mathcal P$ is the lifted ambiguity set of distributions of $(\tilde z, \tilde u)$ with $\mathbb E[\tilde u] = f$, $g(\tilde z) \preccurlyeq_{\mathcal K} \tilde u$ almost surely and $\mathbb P[\tilde z \in \mathcal C_i] \in [\underline p_i, \overline p_i]$, and $\mathcal P'$ is the set of distributions of $\tilde z$ with $\mathbb E[g(\tilde z)] \preccurlyeq_{\mathcal K} f$ and the same probability bounds.
--
--   This is the reverse inclusion of the Lifting Theorem: the auxiliary vector $\tilde u$ can always be projected out without violating the conic moment bound.
--
--   **Formalization Note** The lifted set requires $g(\tilde z)$ to be integrable (an addition to the page; see the goal theorem). Expectations and probabilities of functions of $\tilde z$ under $\mathbb P$ and under its marginal coincide because the marginal is the pushforward by the measurable first projection.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 40, proof of Theorem 5, second inclusion 𝒫′ ⊇ Π_z̃𝒫

import Mathlib
import Definitions.Def_DRConvexOpt_Lifting_Setting

namespace DRConvexOpt.Lifting

open MeasureTheory

/-- Proof of Theorem 5, p. 40: Π_z̃𝒫 ⊆ 𝒫′. -/
theorem marginal_subset_momentSet {nP nM nI : ℕ} (g : (Fin nP → ℝ) → (Fin nM → ℝ))
    (hg : Measurable g) (f : Fin nM → ℝ) (K : Set (Fin nM → ℝ)) (hK : DRConvexOpt.Reform.IsProperCone K)
    (C : Fin nI → Set (Fin nP → ℝ)) (hC : ∀ i, MeasurableSet (C i)) (plo phi : Fin nI → ℝ) :
    marginal (liftedSet g f K C plo phi) ⊆ momentSet g f K C plo phi := by sorry

end DRConvexOpt.Lifting
