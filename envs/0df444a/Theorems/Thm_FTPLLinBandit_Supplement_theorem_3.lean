-- Prove2me | Theorems.Thm_FTPLLinBandit_Supplement_theorem_3
-- name    : FTPLLinBandit.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:42:38.941191+00:00
-- url     : https://prove2.me/theorems/03aae472-898e-4fea-8e37-bfe921daa1e6
-- title:
--   Theorem 3 — no fixed regular perturbation uniformly controls the Hessian on the exposed-edge action set
-- statement:
--   In $\mathbb R^2$, let $e_1,e_2$ be the standard basis, put
--   $$
--   v_i=(\cos(2^{-i}\pi),\sin(2^{-i}\pi))\quad(i\ge2),
--   $$
--   and define the compact convex action set
--   $$
--   A=\operatorname{conv}\big(\{\pm e_1,\pm e_2\}\cup\{v_i:i\ge2\}\big).
--   $$
--   Let $x$ be any fixed measurable argmax selection on $A$, and let $\rho$ be any regular perturbation density. Write $\Psi(\Theta)=\mathbb E[h_A(\Theta+Z)]$ and let $M(\Theta)$ be the covariance of $x(\Theta+Z)$ for $Z\sim\rho$. Then for every finite $c>0$ there is a $\Theta\in\mathbb R^2$ such that
--   $$
--   \nabla^2\Psi(\Theta)\not\preceq cM(\Theta).
--   $$
--   Equivalently, at that $\Theta$ there is a direction $u$ for which $u^\top\nabla^2\Psi(\Theta)u>c\,u^\top M(\Theta)u$.
--
--   This identifies an explicit general action set on which a fixed perturbation cannot provide the uniform covariance comparison available on the simplex.
--
--   **Formalization Note** The Hessian quadratic form is the Fréchet derivative of `gradient (potential A ρ)`. The action covariance is the published centered quadratic form `actCovQ`.
--
--   Differences from the source:
--   - encoding: $x(\Theta)$ is the paper's arbitrary fixed argmax tie-breaking rule → $x$ is any measurable argmax selection; reason: measurability is the convention required for the displayed expectations, and every admissible fixed tie-breaking rule is covered
--   - encoding: $A=\operatorname{conv}(\{\pm e_1,\pm e_2\}\cup\{v_i:i\ge2\})\subset\mathbb R^2$ → the same infinite generating set inside `convexHull ℝ` on `EuclideanSpace ℝ (Fin 2)`; reason: this is the Lean representation of the printed set, with no truncation or closure added
--   - encoding: $\nabla^2\Psi(\Theta)\not\preceq cM(\Theta)$ → the negation of the quadratic-form inequality for every direction $u$, using the Fréchet derivative of the gradient; reason: symmetric matrix order is equivalent to pointwise quadratic-form order
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Theorem 3, p.5 (proof pp.25–26)

import Mathlib
import Definitions.Def_FTPLLinBandit_IsArgmaxSel
import Definitions.Def_FTPLLinBandit_IsRegularDensity
import Definitions.Def_FTPLLinBandit_potential
import Definitions.Def_FTPLLinBandit_actCovQ

open MeasureTheory
open scoped InnerProductSpace

namespace FTPLLinBandit.Supplement

/-- **Theorem 3 (no fixed regular perturbation controls the Hessian on the exposed-edge action
set).** Wei, *Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action
Sets*, arXiv:2610.17818, Theorem 3, p.5 (proof pp.25–26).

Let `e₁,e₂` be the standard basis of `ℝ²`, put
`vᵢ = (cos (2⁻ⁱπ), sin (2⁻ⁱπ))` for every integer `i ≥ 2`, and let `A` be the convex
hull of `{ ±e₁, ±e₂ } ∪ {vᵢ : i ≥ 2}`. For every regular perturbation density `ρ`, every
measurable fixed argmax selection `x`, and every finite `c > 0`, there is a `Θ` at which the
Hessian of the smoothed support function is not dominated by `c` times the covariance of
`x (Θ + Z)`: equivalently, quadratic-form domination fails in some direction `u`.

**Formalization Note.** `ℝ²` is `EuclideanSpace ℝ (Fin 2)`. The infinite generating set is
used exactly; no closure or finite truncation is inserted. The Hessian quadratic form is read
from the actual Fréchet derivative of `gradient (potential A ρ)`. Lemma 18 proves that this is
the derivative of the action mean for every regular `ρ`. The conclusion is the negation of
the universal quadratic-form inequality, so the witnessing direction may depend on `Θ`, `c`,
`ρ`, and the selection `x`. -/
theorem theorem_3 :
    let e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
    let e₂ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
    let v : ℕ → EuclideanSpace ℝ (Fin 2) := fun i =>
      Real.cos ((2 : ℝ) ^ (-(i : ℤ)) * Real.pi) • e₁ +
        Real.sin ((2 : ℝ) ^ (-(i : ℤ)) * Real.pi) • e₂
    let A : Set (EuclideanSpace ℝ (Fin 2)) :=
      convexHull ℝ ({e₁, -e₁, e₂, -e₂} ∪ {a | ∃ i : ℕ, 2 ≤ i ∧ a = v i})
    ∀ (x : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)), IsArgmaxSel A x →
      ∀ (ρ : EuclideanSpace ℝ (Fin 2) → ℝ), IsRegularDensity ρ →
        ∀ c : ℝ, 0 < c → ∃ Θ : EuclideanSpace ℝ (Fin 2),
          ¬∀ u : EuclideanSpace ℝ (Fin 2),
            ⟪u, (fderiv ℝ (gradient (potential A ρ)) Θ) u⟫_ℝ ≤
              c * actCovQ x ρ Θ u := by sorry

end FTPLLinBandit.Supplement
