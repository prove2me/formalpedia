-- Prove2me | Theorems.Thm_DRConvexOpt_Lifting_momentSet_subset_marginal
-- name    : DRConvexOpt.Lifting.momentSet_subset_marginal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:31:43.823348+00:00
-- url     : https://prove2.me/theorems/7a8535a1-3811-4eaa-8852-5fa64b9b17a1
-- title:
--   Proof of Theorem 5, p. 40 — every 𝒫′ distribution is the z̃-marginal of its lift by ũ = g(z̃) − E[g(z̃)] + f
-- statement:
--   Let $g : \mathbb R^P \to \mathbb R^M$ be measurable, $f \in \mathbb R^M$, $\mathcal K \subseteq \mathbb R^M$ a proper cone, and $\mathcal C_i \subseteq \mathbb R^P$, $i \in \mathcal I$, measurable sets with bounds $\underline p_i, \overline p_i$. Let $\mathbb P'$ be a distribution in the moment set $\mathcal P'$, that is, $g(\tilde z)$ is $\mathbb P'$-integrable, $\mathbb E_{\mathbb P'}[g(\tilde z)] \preccurlyeq_{\mathcal K} f$ and $\mathbb P'[\tilde z \in \mathcal C_i] \in [\underline p_i, \overline p_i]$ for all $i$. Let $\mathbb P$ be the joint law of $(\tilde z, \tilde u)$ where $\tilde z \sim \mathbb P'$ and
--   $$
--   \tilde u = g(\tilde z) - \mathbb E_{\mathbb P'}[g(\tilde z)] + f,
--   $$
--   i.e. the pushforward of $\mathbb P'$ under $z \mapsto (z,\, g(z) - \mathbb E_{\mathbb P'}[g(\tilde z)] + f)$. Then $\mathbb P$ belongs to the lifted set $\mathcal P$ and $\Pi_{\tilde z}\mathbb P = \mathbb P'$.
--
--   This is the inclusion $\mathcal P' \subseteq \Pi_{\tilde z}\mathcal P$ of the Lifting Theorem, stated together with the explicit lift used in the paper.
--
--   **Formalization Note** The lift is written as `ν.map (fun z => (z, g z - ∫ z', g z' ∂ν + f))`. Measurability of $g$ makes this map measurable, so the pushforward is a probability measure; measurability of the $\mathcal C_i$ makes their probabilities transfer. The cone hypothesis is carried as on the page.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 40, proof of Theorem 5, first inclusion 𝒫′ ⊆ Π_z̃𝒫

import Mathlib
import Definitions.Def_DRConvexOpt_Lifting_Setting

namespace DRConvexOpt.Lifting

open MeasureTheory

/-- Proof of Theorem 5, p. 40: every ν ∈ 𝒫′ is the z̃-marginal of the pushforward of ν under
z ↦ (z, g(z) − E_ν[g(z̃)] + f), and that pushforward lies in the lifted set 𝒫. -/
theorem momentSet_subset_marginal {nP nM nI : ℕ} (g : (Fin nP → ℝ) → (Fin nM → ℝ))
    (hg : Measurable g) (f : Fin nM → ℝ) (K : Set (Fin nM → ℝ)) (hK : DRConvexOpt.Reform.IsProperCone K)
    (C : Fin nI → Set (Fin nP → ℝ)) (hC : ∀ i, MeasurableSet (C i)) (plo phi : Fin nI → ℝ)
    (ν : Measure (Fin nP → ℝ)) (hν : ν ∈ momentSet g f K C plo phi) :
    ν.map (fun z => (z, g z - ∫ z', g z' ∂ν + f)) ∈ liftedSet g f K C plo phi ∧
      (ν.map (fun z => (z, g z - ∫ z', g z' ∂ν + f))).map Prod.fst = ν := by sorry

end DRConvexOpt.Lifting
