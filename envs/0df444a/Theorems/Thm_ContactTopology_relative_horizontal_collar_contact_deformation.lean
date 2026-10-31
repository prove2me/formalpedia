-- Prove2me | Theorems.Thm_ContactTopology_relative_horizontal_collar_contact_deformation
-- name    : ContactTopology.relative_horizontal_collar_contact_deformation
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-30T19:11:31.242005+00:00
-- url     : https://prove2.me/theorems/fed7ccbd-5421-4388-b795-ef0caff16771
-- title:
--   Relative contact-form deformation for compact horizontal collar perturbations
-- statement:
--   Let $\alpha_0=a_0\cdot d\mathbf y$ be a smooth positive contact form on $\mathbb R^3$, let $b=(b_1,b_2):\mathbb R^2\to\mathbb R^2$ and $\chi:\mathbb R\to\mathbb R$ be smooth, and put
--   $$
--   \delta=\chi(z)\bigl(b_1(x,y)\,dx+b_2(x,y)\,dy\bigr),\qquad
--   \alpha_1=\alpha_0+\delta.
--   $$
--   Suppose $\alpha_1$ is also positive contact and $\delta$ vanishes outside a compact set $K\subset\mathbb R^3$. In coefficient notation, positivity means $a_i\cdot\operatorname{curl}(a_i)>0$.
--
--   There exist a smooth ambient isotopy $\psi_t$ of $\mathbb R^3$, a jointly smooth inverse family $\rho_t$, and jointly smooth positive functions $\lambda_t$ such that $\psi_0=\mathrm{id}$ and
--   $$
--   \psi_t^*\alpha_t=\lambda_t\alpha_0\quad(0\le t\le1),\qquad
--   \psi_1^*\alpha_1=\lambda_1\alpha_0,
--   $$
--   where $\alpha_t=(1-s(t))\alpha_0+s(t)\alpha_1$ and $s$ is the standard smooth transition with $s(0)=0$ and $s(1)=1$. Every spatial differential is injective. Every point outside $K$ stays fixed; more strongly, every point where $\delta$ itself vanishes stays fixed for the whole isotopy. The smooth families extend to all real times.
--
--   This is a relative ambient deformation identifying varying contact forms, suitable as a local analytic tool for convex-surface arguments. It does not establish the full Giroux realization theorem, bypass existence, tight-solid-torus classification, or the Legendrian core classification theorem.
-- source:
--   Explicit coordinate specialization and relative compact-support extension of the Moser argument in Hansjorg Geiges, Contact Geometry, arXiv:math/0307242v2, https://arxiv.org/abs/math/0307242, Section 2.2, Lemma 2.19 and proof of Theorem 2.20. Horizontal collar interpolation is a direct calculation in the invariant collar coordinates reviewed by Hyunki Min, https://arxiv.org/abs/2207.03590v2, Section 2.2, proof of Lemma 2.7. The exact compact-support and horizontal-perturbation statement is the present coordinate consequence, not a claim that either source states this verbatim.

import Mathlib
open Set Function
open scoped ContDiff

theorem ContactTopology.relative_horizontal_collar_contact_deformation
    (a₀ : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (b : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (χ : ℝ → ℝ)
    (h₀ : ContDiff ℝ ∞ a₀) (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ)
    (K : Set (Fin 3 → ℝ)) (hK : IsCompact K) :
    let d : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y =>
      ![χ (y 2)*b ![y 0,y 1] 0,χ (y 2)*b ![y 0,y 1] 1,0]
    let a₁ : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => a₀ y+d y
    let C : ((Fin 3 → ℝ) → (Fin 3 → ℝ)) → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
      fun a y => ![fderiv ℝ a y (Pi.single 1 1) 2-fderiv ℝ a y (Pi.single 2 1) 1,
        fderiv ℝ a y (Pi.single 2 1) 0-fderiv ℝ a y (Pi.single 0 1) 2,
        fderiv ℝ a y (Pi.single 0 1) 1-fderiv ℝ a y (Pi.single 1 1) 0]
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    let A : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun p =>
      (1-Real.smoothTransition p.1) • a₀ p.2+Real.smoothTransition p.1 • a₁ p.2
    (∀ y, 0 < B (a₀ y) (C a₀ y)) →
    (∀ y, 0 < B (a₁ y) (C a₁ y)) →
    (∀ y, y ∉ K → d y = 0) →
    ∃ ψ ρ : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ lam : ℝ → (Fin 3 → ℝ) → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => lam p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) ∧
      (∀ t y, y ∉ K → ψ t y = y) ∧
      (∀ y, d y = 0 → ∀ t, ψ t y = y) ∧
      (∀ t y, 0 < lam t y) ∧
      (∀ t y, Injective (fderiv ℝ (ψ t) y)) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y v,
        B (A (t,ψ t y)) (fderiv ℝ (ψ t) y v) = lam t y*B (a₀ y) v) ∧
      ∀ y v, B (a₁ (ψ 1 y)) (fderiv ℝ (ψ 1) y v) = lam 1 y*B (a₀ y) v := by sorry
