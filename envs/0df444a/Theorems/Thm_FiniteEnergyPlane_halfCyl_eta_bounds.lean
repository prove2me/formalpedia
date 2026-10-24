-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_eta_bounds
-- name    : FiniteEnergyPlane.halfCyl_eta_bounds
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-23T15:53:02.689177+00:00
-- url     : https://prove2.me/theorems/710fae5d-5ec9-476f-8522-c4a775bf7dd1
-- title:
--   Exponential growth-rate convergence controls $\partial_s\zeta-\mu\zeta$ for linear Cauchy–Riemann solutions
-- statement:
--   Let $S:\mathbb{R}^2\to\mathbb{R}^{2n\times 2n}$ be $C^\infty$ and $1$-periodic in $t$, and let $S_\infty$ be a smooth $1$-periodic loop of symmetric matrices such that $S(s,t)\to S_\infty(t)$ exponentially fast in $C^\infty$ with rate $d>0$. Let $\zeta$ be a smooth, $t$-periodic solution of $\partial_s\zeta + J_0\partial_t\zeta + S\zeta = 0$ on $(0,\infty)\times\mathbb{R}$. Put
--   $$F(s)=\int_0^1|\zeta(s,t)|^2\,dt,\qquad \alpha(s)=\frac{\int_0^1\langle\zeta,\partial_s\zeta\rangle(s,t)\,dt}{F(s)},\qquad q(s)=\frac{\int_0^1|\partial_s\zeta(s,t)|^2\,dt}{F(s)}-\alpha(s)^2 .$$
--   Assume that for some $\mu\in\mathbb{R}$, $a>0$, $K$, $s_1>0$ and all $s\ge s_1$ we have $F(s)>0$, $|\alpha(s)-\mu|\le Ke^{-as}$, and $\int_s^T q\le Ke^{-as}$ for all $T\ge s$. Then $\eta=\partial_s\zeta-\mu\zeta$ satisfies, for some $s_0$, $b>0$, $K'$ and all $s\ge s_0$,
--   $$\int_0^1|\eta(s,t)|^2\,dt\le K'e^{-bs}F(s),\qquad \int_0^1|\partial_s\eta(s,t)|^2\,dt\le K'F(s).$$
--   This is the energy-estimate step in the proof of the linear asymptotic formula (Wendl Thm. 4.8.2). It turns exponential convergence of the $L^2$ growth rate $\alpha$ into $L^2$ control of $\partial_s\zeta-\mu\zeta$ relative to the size of $\zeta$.
-- source:
--   Wendl, Lectures on Symplectic Field Theory (2026 notes), proof of Theorem 4.8.2 (linear asymptotic formula); U. Hryniewicz, J. Symplectic Geom. 12 (2014), proof of Theorem 2.11 (the $L^2$ estimates for $\eta=\partial_s\zeta-\mu\zeta$ once $\alpha\to\mu$ exponentially)

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open scoped ContDiff RealInnerProductSpace

/-- Stage of Wendl, Prop. 4.8.2 / Hryniewicz, Thm. 2.11: let `ζ` solve the linear Cauchy–Riemann
equation on a half-cylinder with `S → S∞` exponentially. With `F(s) = ∫₀¹ |ζ(s,t)|² dt`,
`α(s) = ⟨ζ, ∂ₛζ⟩_{L²} / F(s)` and `q(s) = ‖∂ₛζ‖²_{L²} / F(s) - α(s)²`, suppose that for `s ≥ s₁`,
`F > 0`, `|α(s) - μ| ≤ K e^{-as}` and `∫ₛᵀ q ≤ K e^{-as}`. Then `η = ∂ₛζ - μζ` satisfies
`‖η(s)‖²_{L²} ≤ K' e^{-bs} F(s)` and `‖∂ₛη(s)‖²_{L²} ≤ K' F(s)` for large `s`. -/
theorem halfCyl_eta_bounds {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (μ a K s₁ : ℝ) (ha : 0 < a) (hs₁ : 0 < s₁)
    (hF : ∀ s ≥ s₁, 0 < ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2)
    (hα : ∀ s ≥ s₁,
      |(∫ t in (0:ℝ)..1, ⟪ζ (s, t), fderiv ℝ ζ (s, t) (1, 0)⟫) / (∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2)
        - μ| ≤ K * Real.exp (-(a * s)))
    (hq : ∀ s ≥ s₁, ∀ T ≥ s, ∫ x in s..T,
        ((∫ t in (0:ℝ)..1, ‖fderiv ℝ ζ (x, t) (1, 0)‖ ^ 2) / (∫ t in (0:ℝ)..1, ‖ζ (x, t)‖ ^ 2) -
          ((∫ t in (0:ℝ)..1, ⟪ζ (x, t), fderiv ℝ ζ (x, t) (1, 0)⟫) /
            (∫ t in (0:ℝ)..1, ‖ζ (x, t)‖ ^ 2)) ^ 2) ≤ K * Real.exp (-(a * s))) :
    ∃ s₀ : ℝ, ∃ b > 0, ∃ K' : ℝ, ∀ s ≥ s₀,
      ∫ t in (0:ℝ)..1, ‖fderiv ℝ ζ (s, t) (1, 0) - μ • ζ (s, t)‖ ^ 2 ≤
        K' * Real.exp (-(b * s)) * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 ∧
      ∫ t in (0:ℝ)..1, ‖fderiv ℝ (fun p => fderiv ℝ ζ p (1, 0) - μ • ζ p) (s, t) (1, 0)‖ ^ 2 ≤
        K' * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 := by sorry

end FiniteEnergyPlane
