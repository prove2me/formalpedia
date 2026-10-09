-- Prove2me | Theorems.Thm_DRConvexOpt_InfConv_chain
-- name    : DRConvexOpt.InfConv.chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:33.633705+00:00
-- url     : https://prove2.me/theorems/66be8c43-7139-4957-b98e-6052c0eef61d
-- title:
--   Proof of Theorem 3, p. 37 — for (y, δ) ∈ Γ(x), Σ δ_j sup_{𝒫^j} E[v(y_j/δ_j)] ≥ Σ δ_j sup_𝒫 E[v(y_j/δ_j)] ≥ sup_𝒫 E[v(x)]
-- statement:
--   Let $\mathcal P$ be the standardized ambiguity set, $\mathcal P^j$ its outer approximations for a partition $\{\mathcal I_j\}_{j \in \mathcal J}$, and $v$ a piecewise bi-affine function as in (C3). Fix $x \in \mathbb R^N$. Then every $(y,\delta) \in \Gamma(x)$ satisfies
--   $$\sum_{j\in\mathcal J} \delta_j \sup_{\mathbb P\in\mathcal P^j} \mathbb E_{\mathbb P}[v(y_j/\delta_j,\tilde z)] \;\ge\; \sum_{j\in\mathcal J} \delta_j \sup_{\mathbb P\in\mathcal P} \mathbb E_{\mathbb P}[v(y_j/\delta_j,\tilde z)] \;\ge\; \sup_{\mathbb P\in\mathcal P} \mathbb E_{\mathbb P}[v(x,\tilde z)],$$
--   with all suprema taken in the extended reals.
--
--   This chain is the core of the implication (7) $\Rightarrow$ (3) in Theorem 3.
--
--   **Formalization Note** The two inequalities are stated as a conjunction (the middle term first compared with the left, then with the right). The identity $\sup_{\mathbb P} \mathbb E_{\mathbb P}[v(\sum_j y_j,\tilde z)] = \sup_{\mathbb P} \mathbb E_{\mathbb P}[v(x,\tilde z)]$ of the page is the constraint $\sum_j y_j = x$ of $\Gamma(x)$. Suprema are `EReal`-valued ($\sup\emptyset = -\infty$), and products $\delta_j \cdot s$ use $\delta_j > 0$. No standing condition is needed.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 37, proof of Theorem 3, first display

import Mathlib
import Definitions.Def_DRConvexOpt_InfConv_Setting

namespace DRConvexOpt.InfConv

open MeasureTheory Matrix Filter Topology

/-- Proof of Theorem 3, p. 37, the chain display: for every `(y, δ) ∈ Γ(x)`,
`∑_j δ_j sup_{𝒫^j} E[v(y_j/δ_j, z̃)] ≥ ∑_j δ_j sup_{𝒫} E[v(y_j/δ_j, z̃)] ≥ sup_{𝒫} E[v(x, z̃)]`
(the identity `∑_j y_j = x` is built into `Γ(x)`). -/
theorem chain {nP nQ nK nI nN nL nJ : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL) (blk : Fin (nI + 1) → Fin nJ)
    (x : Fin nN → ℝ) :
    ∀ p ∈ Gamma x,
      (∑ j, ((p.2 j : ℝ) : EReal) *
          worstCase (ambiguitySet d) (fun ω => v.eval ((p.2 j)⁻¹ • p.1 j) ω.1) ≤
        ∑ j, ((p.2 j : ℝ) : EReal) *
          worstCase (outerSet d blk j) (fun ω => v.eval ((p.2 j)⁻¹ • p.1 j) ω.1)) ∧
      worstCase (ambiguitySet d) (fun ω => v.eval x ω.1) ≤
        ∑ j, ((p.2 j : ℝ) : EReal) *
          worstCase (ambiguitySet d) (fun ω => v.eval ((p.2 j)⁻¹ • p.1 j) ω.1) := by sorry

end DRConvexOpt.InfConv
