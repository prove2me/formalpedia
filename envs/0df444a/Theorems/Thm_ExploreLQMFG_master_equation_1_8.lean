-- Prove2me | Theorems.Thm_ExploreLQMFG_master_equation_1_8
-- name    : ExploreLQMFG.master_equation_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:55.558269+00:00
-- url     : https://prove2.me/theorems/3f5fce88-ea54-4d14-a54d-754c389e7712
-- title:
--   (1.8), p.4 — the master equation has a unique classical solution with bounded derivatives
-- statement:
--   Let $d\ge1$, $T>0$, let $Q,R$ be $d\times d$ real matrices, let $f,g:\mathbb R^d\to\mathbb R^d$ be bounded and Lipschitz, let $\eta$ solve the Riccati equation (2.3), and let $\varepsilon>0$. Then the master equation
--   $$\partial_t\theta(t,x)+\frac{\varepsilon^2}2\Delta_x\theta(t,x)-\big(\eta_tx+\theta(t,x)\big)\cdot\nabla_x\theta(t,x)+Q^\dagger f(x)-\eta_t\theta(t,x)=0,\qquad \theta(T,\cdot)=R^\dagger g,$$
--   has a classical solution $\theta:[0,T]\times\mathbb R^d\to\mathbb R^d$ with bounded $\theta$ and $\nabla_x\theta$, and any two such solutions coincide on $[0,T]\times\mathbb R^d$.
--
--   When $\varepsilon>0$ the equation is uniformly parabolic; the solution $\theta_\varepsilon$ decouples the forward–backward system (1.7) and represents the limit of the scheme through (2.18).
--
--   Differences from the source:
--   - reading: 'a unique classical solution (with bounded derivatives)' → the class IsClassicalSol: continuous on [0, T] × ℝᵈ, C^{1,2} on [0, T) × ℝᵈ, θ and ∇ₓθ bounded on [0, T) × ℝᵈ; reason: g is only Lipschitz, so higher derivatives cannot be bounded up to T; Lemma 2.8 bounds ∇ₓθ on [0, T)
--   - encoding: ℝᵈ with the Euclidean norm |·|; |·| on d × d matrices unnamed → Fin d → ℝ with |x|² = Σᵢ xᵢ² written explicitly; matrices carry the Frobenius norm; reason: Mathlib's default norm on Fin d → ℝ is the sup norm; all matrix norms are equivalent up to a factor depending only on d, which the constants absorb
-- source:
--   Delarue & Vasileiadis, Exploration Noise for Learning Linear-Quadratic Mean Field Games, arXiv:2107.00839v2 (https://arxiv.org/abs/2107.00839v2), §1.2, paragraph after (1.8), p.4

import Mathlib
import Definitions.Def_ExploreLQMFG_Master

open MeasureTheory Filter
open scoped NNReal Matrix

namespace ExploreLQMFG

/-- **Classical solvability of the master equation (1.8)** (Delarue & Vasileiadis,
arXiv:2107.00839v2, §1.2, paragraph after (1.8), p.4): "When ε > 0, the PDE is uniformly
parabolic and hence has a unique classical solution (with bounded derivatives)."

Here `d ≥ 1`, `T > 0`, `Q, R` are `d × d` real matrices, `f, g : ℝᵈ → ℝᵈ` are bounded and
Lipschitz (§1.9.1, p.18), `η` solves the Riccati equation (2.3) (p.20), and `ε > 0`. Then (1.8)
with terminal condition `θ(T, ·) = R†g` has a classical solution in the class `IsClassicalSol`,
and any two such solutions coincide on `[0, T] × ℝᵈ`.

**Formalization Note.** "Classical solution (with bounded derivatives)" is read as
`IsClassicalSol`: continuous on `[0, T] × ℝᵈ`, `C^{1,2}` on `[0, T) × ℝᵈ`, with `θ` and `∇ₓθ`
bounded on `[0, T) × ℝᵈ`. -/
theorem master_equation_1_8 {d : ℕ} (hd : 0 < d) (T : ℝ≥0) (hT : 0 < T)
    (Q R : Matrix (Fin d) (Fin d) ℝ) (f g : (Fin d → ℝ) → (Fin d → ℝ))
    (hf : IsBddLip f) (hg : IsBddLip g) (ε : ℝ) (hε : 0 < ε)
    (η : ℝ → Matrix (Fin d) (Fin d) ℝ) (hη : IsRiccatiSol Q R T η) :
    (∃ θ, IsClassicalSol T ε η (tmul Q f) (tmul R g) θ) ∧
      ∀ θ₁ θ₂, IsClassicalSol T ε η (tmul Q f) (tmul R g) θ₁ →
        IsClassicalSol T ε η (tmul Q f) (tmul R g) θ₂ →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, θ₁ t x = θ₂ t x := by sorry

end ExploreLQMFG
