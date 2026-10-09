-- Prove2me | Theorems.Thm_DRConvexOpt_Reform_moment_duality
-- name    : DRConvexOpt.Reform.moment_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:49.07637+00:00
-- url     : https://prove2.me/theorems/7b55479a-a564-48b3-8ab2-bc49dba5d926
-- title:
--   Proof of Theorem 1, p. 35 — (3) holds iff the dual of the moment problem has a feasible (β, κ, λ) of value at most w
-- statement:
--   Let $\mathcal P$ be the standardized ambiguity set (4) with proper cones $\mathcal K_i$ and bounds $0 \le \underline p_i \le \overline p_i \le 1$, satisfying (C1): $\mathcal C_I$ is bounded and $\underline p_I = \overline p_I = 1$. Assume moreover the moment-problem regularity condition (S1) (see the Setting). Let $v$ satisfy (C3), $x \in \mathbb R^N$ and $w \in \mathbb R$. Then
--   $$\mathbb E_{\mathbb P}[v(x,\tilde z)] \le w \quad \forall \mathbb P \in \mathcal P$$
--   holds if and only if there are $\beta \in \mathbb R^K$ and $\kappa, \lambda \in \mathbb R^I_+$ with
--   $$b^\top\beta + \sum_{i \in \mathcal I}\big[\overline p_i \kappa_i - \underline p_i \lambda_i\big] \le w, \qquad [Az + Bu]^\top \beta + \sum_{i \in \mathcal I} \mathbf 1_{[(z,u) \in \mathcal C_i]}\,[\kappa_i - \lambda_i] \ge v(x,z) \quad \forall (z,u) \in \mathcal C_I.$$
--
--   This is the duality step of the proof of Theorem 1: the worst-case expectation is the value of a moment problem over nonnegative measures on $\mathcal C_I$, and strong duality with dual attainment lets the robust constraint be certified by a dual feasible point.
--
--   **Formalization Note** The paper justifies strong duality by "Proposition 3.4 in [56], which is applicable due to condition (C2)". Condition (C2) only makes the probability bounds strictly feasible and says nothing about $\mathbb E_{\mathbb P}[A\tilde z + B\tilde u] = b$; with $\mathcal C_1$ the unit disk, $\mathbb E[\tilde z_1] = 1$ and $v = z_2$ the dual has no solution of value $\le 0$ although (3) holds with $w = 0$. The statement therefore assumes (S1), Robinson's constraint qualification for the moment problem, in place of (C2). The "if" direction needs none of it.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 35, proof of Theorem 1: the moment problem, its dual, and the strong duality sentence

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting

namespace DRConvexOpt.Reform

open MeasureTheory Matrix

/-- Proof of Theorem 1, p. 35: the dual of the moment problem, with strong duality. Under (C1),
the standing assumptions on the cones and on `p̲, p̄`, and the disclosed assumption (S1)
`MomentSlater` (in place of the page's appeal to (C2)), the constraint (3) holds iff the dual of
the moment problem has a feasible `(β, κ, λ)` with objective value at most `w`. -/
theorem moment_duality {nP nQ nK nI nN nL : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL)
    (hK : ∀ i, IsProperCone (d.K i))
    (hp : ∀ i, 0 ≤ d.plo i ∧ d.plo i ≤ d.phi i ∧ d.phi i ≤ 1)
    (hC1 : Bornology.IsBounded (d.conf (Fin.last nI)) ∧ d.plo (Fin.last nI) = 1 ∧
      d.phi (Fin.last nI) = 1)
    (hS1 : MomentSlater d) (x : Fin nN → ℝ) (w : ℝ) :
    (∀ μ ∈ ambiguitySet d, ∫ ω, v.eval x ω.1 ∂μ ≤ w) ↔
    ∃ (β : Fin nK → ℝ) (κ lam : Fin (nI + 1) → ℝ), (∀ i, 0 ≤ κ i) ∧ (∀ i, 0 ≤ lam i) ∧
      d.b ⬝ᵥ β + ∑ i, (d.phi i * κ i - d.plo i * lam i) ≤ w ∧
      ∀ ω ∈ d.conf (Fin.last nI),
        v.eval x ω.1 ≤ (d.A *ᵥ ω.1 + d.B *ᵥ ω.2) ⬝ᵥ β +
          ∑ i, (d.conf i).indicator (fun _ => (1 : ℝ)) ω * (κ i - lam i) := by sorry

end DRConvexOpt.Reform
