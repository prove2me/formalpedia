-- Prove2me | Theorems.Thm_DRConvexOpt_Reform_theorem_1_if
-- name    : DRConvexOpt.Reform.theorem_1_if
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:06.911306+00:00
-- url     : https://prove2.me/theorems/ab529e4f-34cf-4cc8-8141-6765db65b433
-- title:
--   Theorem 1, sufficiency, pp. 10–11 — a solution of the conic system implies the distributionally robust constraint (3)
-- statement:
--   Let $\mathcal P$ be the standardized ambiguity set (4) whose confidence sets (5) are defined by proper cones $\mathcal K_i$, satisfying (C1) ($\mathcal C_I$ bounded, $\underline p_I = \overline p_I = 1$) and the nesting condition (N). Let $v$ satisfy (C3), $x \in \mathbb R^N$ and $w \in \mathbb R$. If there are $\beta \in \mathbb R^K$, $\kappa, \lambda \in \mathbb R^I_+$ and $\phi_{il} \in \mathcal K_i^\star$, $i \in \mathcal I$, $l \in \mathcal L$, with
--   $$\begin{aligned} & b^\top\beta + \sum_{i \in \mathcal I}\big[\overline p_i\kappa_i - \underline p_i \lambda_i\big] \le w,\\ & c_i^\top \phi_{il} + s_l^\top x + t_l \le \sum_{i' \in \mathcal A(i)}[\kappa_{i'} - \lambda_{i'}],\\ & C_i^\top\phi_{il} + A^\top \beta = S_l^\top x + \mathbf t_l,\\ & D_i^\top \phi_{il} + B^\top\beta = 0 \end{aligned} \qquad \forall i \in \mathcal I,\ \forall l \in \mathcal L,$$
--   then the distributionally robust constraint (3) holds:
--   $$\mathbb E_{\mathbb P}[v(x,\tilde z)] \le w \qquad \forall \mathbb P \in \mathcal P.$$
--
--   This is the half of Theorem 1 that makes the conic system a safe (conservative) replacement for (3); it is weak duality and holds without the regularity condition (C2).
--
--   **Formalization Note** In the second line $t_l$ is the scalar `v.t0 l`; in the third, $\mathbf t_l$ is the vector `v.tv l`. Indices are 0-based. The hypothesis (C2) and the standing bounds $0 \le \underline p_i \le \overline p_i \le 1$ (p. 8) are dropped; neither is used by this half, so dropping them only strengthens the statement.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), pp. 10–11, Theorem 1 (the "if" direction)

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting

namespace DRConvexOpt.Reform

open MeasureTheory Matrix

/-- Theorem 1, sufficiency ("if" half), pp. 10–11: under (C1), (C3) and (N) (and the standing
assumption that every `K_i` is a proper cone), a solution of the conic system implies the
distributionally robust constraint (3). (C2) is not needed for this half. -/
theorem theorem_1_if {nP nQ nK nI nN nL : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL)
    (hK : ∀ i, IsProperCone (d.K i))
    (hC1 : Bornology.IsBounded (d.conf (Fin.last nI)) ∧ d.plo (Fin.last nI) = 1 ∧
      d.phi (Fin.last nI) = 1)
    (hN : Nesting d) (x : Fin nN → ℝ) (w : ℝ) :
    (∃ (β : Fin nK → ℝ) (κ lam : Fin (nI + 1) → ℝ)
      (φ : (i : Fin (nI + 1)) → Fin nL → Fin (d.L i) → ℝ),
      (∀ i, 0 ≤ κ i) ∧ (∀ i, 0 ≤ lam i) ∧ (∀ i l, φ i l ∈ dualCone (d.K i)) ∧
      d.b ⬝ᵥ β + ∑ i, (d.phi i * κ i - d.plo i * lam i) ≤ w ∧
      ∀ i l, d.c i ⬝ᵥ φ i l + v.s l ⬝ᵥ x + v.t0 l ≤ ∑ i' ∈ anc d i, (κ i' - lam i') ∧
        (d.C i)ᵀ *ᵥ φ i l + d.Aᵀ *ᵥ β = (v.S l)ᵀ *ᵥ x + v.tv l ∧
        (d.D i)ᵀ *ᵥ φ i l + d.Bᵀ *ᵥ β = 0) →
    ∀ μ ∈ ambiguitySet d, ∫ ω, v.eval x ω.1 ∂μ ≤ w := by sorry

end DRConvexOpt.Reform
