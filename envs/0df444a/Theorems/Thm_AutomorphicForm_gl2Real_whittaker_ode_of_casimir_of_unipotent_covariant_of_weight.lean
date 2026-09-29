-- Prove2me | Theorems.Thm_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight
-- name    : AutomorphicForm.gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/eb790e33-1e79-5291-8f8f-4c8ccf40524e
-- title:
--   Whittaker's equation from the Casimir eigenrelation on GL₂(ℝ)
-- statement:
--   Let $F\colon \mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$, let $\varepsilon\in\mathbb{R}$ with $\varepsilon=1$ or $\varepsilon=-1$, let $n\in\mathbb{Z}$ and let $\lambda,\nu\in\mathbb{C}$ satisfy $\nu^2=\tfrac14-\lambda$. Suppose given functions $DF(d,\cdot)$ for $d$ ranging over the three directions $H$, $E$, $Fm$ of `ArchDir`, and functions $DHH$, $DEF$, such that at every $h$ the curve $t\mapsto F(h\cdot \mathrm{archFlowMatrix}(d,t))$ has derivative $DF(d,h)$ at $t=0$, where the flows are $\mathrm{diag}(e^t,e^{-t})$ for $H$, the upper unipotent $\binom{1\ t}{0\ 1}$ for $E$ and the lower unipotent $\binom{1\ 0}{t\ 1}$ for $Fm$; and such that $t\mapsto DF(H,h\cdot\mathrm{diag}(e^t,e^{-t}))$ has derivative $DHH(h)$ at $0$, while $t\mapsto DF(Fm,h\cdot\binom{1\ t}{0\ 1})$ has derivative $DEF(h)$ at $0$. Assume the Casimir relation $-\bigl(\tfrac14 DHH(h)-\tfrac12 DF(H,h)+DEF(h)\bigr)=\lambda F(h)$ for all $h$; the covariance $F\bigl(\binom{1\ x}{0\ 1}h\bigr)=e^{2\pi i\varepsilon x}F(h)$ for all $x\in\mathbb{R}$ and $h$; and the right equivariance $F(hk)=\mathrm{archWeightChar}_{\mathbb{R}}(n)(k)\,F(h)$ for all $k$ in the subgroup `rowIsometrySubgroup₀ ℝ`. Then $f(y):=F(\mathrm{diag}(\sqrt{y},1/\sqrt{y}))$, written as $F(\mathrm{splitTorusGL2}(\tfrac12\log y))$, is differentiable on $(0,\infty)$, so is $f'$, and for every $y>0$ one has $y^2 f''(y)+\bigl(\tfrac14-\nu^2+2\pi\varepsilon n\,y-4\pi^2y^2\bigr)f(y)=0$.
--
--   This is the classical Iwasawa-coordinate computation turning the Casimir eigenvalue equation for a function on $\mathrm{GL}_2(\mathbb{R})$ that is covariant under the upper unipotent subgroup and transforms by the weight-$n$ character of the rotation subgroup into Whittaker's differential equation of weight $\varepsilon n$ for its restriction to the split torus. It is used to show that the Whittaker coefficients of an automorphic form with prescribed archimedean Casimir eigenvalue and archimedean character satisfy the Whittaker equation, whence the growth and uniqueness properties of those coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight
    (F : GL (Fin 2) ℝ → ℂ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (n : ℤ) (lam ν : ℂ) (hν : ν ^ 2 = 1 / 4 - lam)
    (DF : ArchDir → GL (Fin 2) ℝ → ℂ) (DHH DEF : GL (Fin 2) ℝ → ℂ)
    (hD : ∀ (d : ArchDir) (h : GL (Fin 2) ℝ), HasDerivAt (fun t : ℝ => F (h * archFlowMatrix d t)) (DF d h) 0)
    (hDHH : ∀ h : GL (Fin 2) ℝ, HasDerivAt (fun t : ℝ => DF .H (h * archFlowMatrix .H t)) (DHH h) 0)
    (hDEF : ∀ h : GL (Fin 2) ℝ, HasDerivAt (fun t : ℝ => DF .Fm (h * archFlowMatrix .E t)) (DEF h) 0)
    (hΩ : ∀ h : GL (Fin 2) ℝ, -((1 / 4 : ℂ) * DHH h - (1 / 2 : ℂ) * DF .H h + DEF h) = lam * F h)
    (hN : ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
      F (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * (ε * x)) * F h)
    (hK : ∀ (k : GL (Fin 2) ℝ) (hk : k ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
      F (h * k) = ((archWeightCharℝ n ⟨k, hk⟩ : ℂˣ) : ℂ) * F h) :
    let f : ℝ → ℂ := fun y => F (splitTorusGL2 (Real.log y / 2))
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * n : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0 := by sorry
