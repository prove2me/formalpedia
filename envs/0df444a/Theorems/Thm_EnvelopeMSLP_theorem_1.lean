-- Prove2me | Theorems.Thm_EnvelopeMSLP_theorem_1
-- name    : EnvelopeMSLP.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:28:04.222003+00:00
-- url     : https://prove2.me/theorems/751bf69a-8cc8-47fe-91e9-283e82ba3f7c
-- title:
--   Theorem 1 (Takayama) — the envelope formula (2) for an LP with differentiable optimal solutions
-- statement:
--   Let $\Theta\subseteq\mathbb R$ be open, let $A:\Theta\to\mathbb R^{m\times n}$, $b:\Theta\to\mathbb R^m$, $c:\Theta\to\mathbb R^n$ be differentiable, and let
--   $$V(\theta)=\max_x\ \langle c(\theta),x\rangle\quad\text{s.t. }A(\theta)x\le b(\theta),\ x\ge0.$$
--   Suppose $\theta_0\in\Theta$ and that $x^*(\theta)$, $\lambda^*(\theta)$ are optimal primal and dual solutions at every $\theta$ near $\theta_0$, differentiable at $\theta_0$. Then
--   $$V'(\theta_0)=\langle\nabla c(\theta_0),x^*(\theta_0)\rangle+\Big\langle\lambda^*(\theta_0),\nabla b(\theta_0)-\tfrac{d}{d\theta}A(\theta_0)\,x^*(\theta_0)\Big\rangle.$$
--   This is the classical envelope formula: the derivative of the value needs only one optimal primal-dual pair, not the derivative of the solutions.
--
--   **Formalization Note** The primal and dual of form (1) are the published `PrimalOptimal` and `DualOptimal`. The value is read in $\mathbb R$, which is its true value near $\theta_0$ because an optimum exists there.
--
--   Differences from the source:
--   - generalization: x* and λ* continuously differentiable in θ → differentiable at θ₀ only; reason: a C¹ selection is differentiable at θ₀, so the source's case is covered; the proof uses only the derivative at θ₀
--   - reading: for a given θ, the optimal solutions x*(θ), λ*(θ) are differentiable in θ → selections optimal at every θ near θ₀; reason: differentiating a solution in θ presupposes a solution at the nearby θ
--   - encoding: V(θ) real valued → the EReal value read through toReal; reason: an optimum exists near θ₀, so the value is finite there
--   - encoding: A : Θ → R^{m×n}, b : Θ → R^m, c : Θ → R^n → A, b, c defined on all of ℝ, hypotheses on Θ; reason: every hypothesis and conclusion looks only at θ in the open set Θ or near such θ, so values off Θ are never used
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), Theorem 1, display (2), p.5

import Mathlib
import Definitions.Def_EnvelopeMSLP_lpValue
import Definitions.Def_EnvelopeMSLP_lpCurve
import Definitions.Def_EnvelopeMSLP_matDeriv
import Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair
open Matrix Topology

namespace EnvelopeMSLP

/-- **Theorem 1 (Takayama).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), Theorem 1, p.5, display (2). Let `Θ ⊆ ℝ` be open, and let the data of
form (1), `V(θ) = max ⟨c(θ), x⟩ s.t. A(θ) x ≤ b(θ), x ≥ 0`, be differentiable on `Θ`. If `x*` and `λ*`
are optimal primal and dual selections at every point near `θ₀ ∈ Θ`, differentiable at `θ₀`, then
`V′(θ₀) = ⟨c′(θ₀), x*(θ₀)⟩ + ⟨λ*(θ₀), b′(θ₀) − A′(θ₀) x*(θ₀)⟩`.

**Formalization Note.** Form (1) and its dual are the published `PrimalOptimal`, `DualOptimal`.
`V` is `lpValue` read in `ℝ`, which is the true value near `θ₀` since an optimum exists there. The
paper's "continuously differentiable" is weakened to differentiable at `θ₀`. -/
theorem theorem_1 {m n : ℕ} (Θ : Set ℝ) (hΘ : IsOpen Θ)
    (A : ℝ → Matrix (Fin m) (Fin n) ℝ) (b : ℝ → Fin m → ℝ) (c : ℝ → Fin n → ℝ)
    (hdata : ∀ k, DifferentiableOn ℝ (fun θ => lpCurve A b c θ k) Θ)
    (x : ℝ → Fin n → ℝ) (lam : ℝ → Fin m → ℝ) (θ₀ : ℝ) (hθ₀ : θ₀ ∈ Θ)
    (hx : ∀ᶠ θ in 𝓝 θ₀, VanderbeiLP.StrictComp.PrimalOptimal (A θ) (b θ) (c θ) (x θ))
    (hlam : ∀ᶠ θ in 𝓝 θ₀, VanderbeiLP.StrictComp.DualOptimal (A θ) (b θ) (c θ) (lam θ))
    (hxd : DifferentiableAt ℝ x θ₀) (hlamd : DifferentiableAt ℝ lam θ₀) :
    HasDerivAt
      (fun θ => (lpValue {y | VanderbeiLP.StrictComp.PrimalFeasible (A θ) (b θ) y} (c θ)).toReal)
      (deriv c θ₀ ⬝ᵥ x θ₀ + lam θ₀ ⬝ᵥ (deriv b θ₀ - matDeriv A θ₀ *ᵥ x θ₀)) θ₀ := by sorry

end EnvelopeMSLP
