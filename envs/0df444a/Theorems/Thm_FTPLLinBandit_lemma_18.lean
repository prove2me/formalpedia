-- Prove2me | Theorems.Thm_FTPLLinBandit_lemma_18
-- name    : FTPLLinBandit.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:02:25.152628+00:00
-- url     : https://prove2.me/theorems/c9ebeb83-7af2-4581-9a71-735167997563
-- title:
--   Lemma 18 — gradient and Hessian of a smoothed support function: $\nabla\Psi(\Theta)=\mathbb E[x(\Theta+Z)]$, $\nabla^2\Psi(\Theta)=-\int x(z)\nabla\rho(z-\Theta)^\top dz$
-- statement:
--   Let $A\subseteq RB^d_2$, let $h(\Theta)=\max_{a\in A}\langle a,\Theta\rangle$, and let $x$ be an argmax selection of $A$ (so $A$ is nonempty). Let $\rho$ be a regular perturbation density (a locally Lipschitz probability density with $\mathbb E_{Z\sim\rho}\|Z\|_2<\infty$ and $\int\|\nabla\rho\|_2<\infty$) and $\Psi(\Theta)=\mathbb E_{Z\sim\rho}[h(\Theta+Z)]$. Then for every $\Theta\in\mathbb R^d$:
--
--   1. $\Psi$ is differentiable at $\Theta$ with gradient
--   $$\nabla\Psi(\Theta)=\mathbb E_{Z\sim\rho}\big[x(\Theta+Z)\big];$$
--   2. the map $\Theta\mapsto\nabla\Psi(\Theta)$ is (Fréchet) differentiable at $\Theta$, with
--   $$\nabla^2\Psi(\Theta)=-\int_{\mathbb R^d}x(z)\,\nabla\rho(z-\Theta)^\top\,dz,\quad\text{i.e.}\quad \nabla^2\Psi(\Theta)\,u=-\int_{\mathbb R^d}\langle\nabla\rho(z-\Theta),u\rangle\,x(z)\,dz .$$
--
--   The gradient identity gives $\mathbb E_t[a_t\mid\text{no exploration}]=\nabla\Psi_t(\hat\Theta_t)$, and the Hessian identity is the starting point of every stability bound of the paper (Theorems 4, 7 and 10).
--
--   **Formalization Note** The Hessian identity is stated as differentiability of $\Theta\mapsto\mathbb E[x(\Theta+Z)]$, which is $\nabla\Psi$ by item 1 at every point.
--
--   Differences from the source:
--   - generalization: the standing Assumption 1 (rB ⊆ conv A ⊆ RB, ν, Cov(ν) = I/d) → only A ⊆ R·B^d_2, with an argmax selection x of A (which makes A nonempty); reason: Assumption 1 implies A ⊆ conv A ⊆ RB, and the oracle gives the selection; the proof uses only these, so the Lean statement specializes to the paper's
--   - encoding: x(Θ) = argmax with ties broken in an arbitrary but fixed way → any measurable argmax selection x (IsArgmaxSel); reason: every fixed tie-breaking rule is an argmax selection; measurability is the convention under which the paper's expectations of x(Θ + Z) are defined
--   - encoding: ∇²Ψ(Θ) = −∫ x(z)∇ρ(z − Θ)ᵀ dz → the map Θ ↦ E[x(Θ + Z)] has a Fréchet derivative H at Θ with H u = −∫ ⟨∇ρ(z − Θ), u⟩ x(z) dz; reason: by item 1 that map is ∇Ψ, so H is ∇²Ψ(Θ) and the identity is the displayed one applied to u
--   - encoding: ∇ρ, the a.e. gradient of a locally Lipschitz ρ → Mathlib's gradient (0 off the differentiability set); reason: a locally Lipschitz function is differentiable a.e.; same integrals
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Lemma 18, p.26

import Mathlib
import Definitions.Def_FTPLLinBandit_IsArgmaxSel
import Definitions.Def_FTPLLinBandit_IsRegularDensity
import Definitions.Def_FTPLLinBandit_potential
import Definitions.Def_FTPLLinBandit_actMean

open MeasureTheory
open scoped InnerProductSpace

namespace FTPLLinBandit

/-- **Lemma 18 (Hessian of a smoothed support function).** Wei, *Follow the Perturbed Leader for
Linear Bandits: √T Regret over General Action Sets*, arXiv:2610.17818, Lemma 18, p.26: "For a
regular ρ, define Ψ(Θ) = E_{Z∼ρ}[h(Θ + Z)]. Then ∇Ψ(Θ) = E_{Z∼ρ}[x(Θ + Z)],
∇²Ψ(Θ) = −∫_{ℝ^d} x(z)∇ρ(z − Θ)ᵀ dz."

Let `A ⊆ R·B^d_2`, `x` a measurable argmax selection of `A` (so `A` is nonempty), and `ρ` a regular
density. Then at every `Θ`: `Ψ = potential A ρ` has gradient `E_{Z∼ρ}[x(Θ + Z)]`, and this
gradient map is Fréchet differentiable at `Θ` with derivative
`u ↦ −∫ ⟨∇ρ(z − Θ), u⟩ x(z) dz`.

**Formalization Note.** Assumption 1 is replaced by what the proof uses: `A` contained in the ball
of radius `R` ("h(Θ + z) ≤ R‖Θ + z‖₂", "‖x(z)‖₂ ≤ R"), which Assumption 1 implies; `A` is nonempty
because the argmax selection `x` takes values in it. The Hessian identity is stated as Fréchet differentiability of `Θ ↦ E[x(Θ + Z)]` (which is
`∇Ψ` by the first clause, at every point) with the displayed derivative applied to a direction
`u`. -/
theorem lemma_18 {d : ℕ} (A : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ)
    (hAR : A ⊆ Metric.closedBall 0 R)
    (x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hx : IsArgmaxSel A x)
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : IsRegularDensity ρ)
    (Θ : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (potential A ρ) (actMean x ρ Θ) Θ ∧
      ∃ H : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
        HasFDerivAt (actMean x ρ) H Θ ∧
          ∀ u, H u = -∫ z, ⟪gradient ρ (z - Θ), u⟫_ℝ • x z := by sorry

end FTPLLinBandit
