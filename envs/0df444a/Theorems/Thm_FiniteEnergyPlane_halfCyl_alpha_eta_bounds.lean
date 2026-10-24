-- Prove2me | Theorems.Thm_FiniteEnergyPlane_halfCyl_alpha_eta_bounds
-- name    : FiniteEnergyPlane.halfCyl_alpha_eta_bounds
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-23T15:35:39.545842+00:00
-- url     : https://prove2.me/theorems/420c53a6-a15e-4383-90f2-8c320c9a1310
-- title:
--   Exponential convergence of the $L^2$ growth rate for linear Cauchy–Riemann solutions on a half-cylinder
-- statement:
--   Let $S:\mathbb{R}^2\to\mathbb{R}^{2n\times 2n}$ be $C^\infty$ and $1$-periodic in $t$, and let $S_\infty$ be a smooth $1$-periodic loop of symmetric matrices such that $S(s,t)\to S_\infty(t)$ exponentially fast in $C^\infty$ with rate $d>0$. Let $\zeta$ be a smooth, $t$-periodic solution of $\partial_s\zeta + J_0\partial_t\zeta + S\zeta = 0$ on $(0,\infty)\times\mathbb{R}$ that is not identically zero and satisfies $|\zeta(s,t)|\le C e^{\delta_0 s}$.
--
--   Put
--   $$F(s)=\int_0^1|\zeta(s,t)|^2\,dt,\qquad \alpha(s)=\frac{\int_0^1\langle\zeta,\partial_s\zeta\rangle(s,t)\,dt}{F(s)},\qquad q(s)=\frac{\int_0^1|\partial_s\zeta(s,t)|^2\,dt}{F(s)}-\alpha(s)^2 .$$
--   Then there are $\mu\le\delta_0$, $s_0>0$, $a>0$ and $K$ such that for all $s\ge s_0$:
--   - $F(s)>0$;
--   - $|\alpha(s)-\mu|\le Ke^{-as}$;
--   - $\int_s^T q(x)\,dx\le Ke^{-as}$ for every $T\ge s$;
--   - with $\eta=\partial_s\zeta-\mu\zeta$: $\int_0^1|\eta(s,t)|^2dt\le Ke^{-as}F(s)$ and $\int_0^1|\partial_s\eta(s,t)|^2dt\le K\,F(s)$.
--
--   This is the $L^2$ part of the proof of the linear asymptotic formula (Wendl Thm. 4.8.2): $\alpha=F'/(2F)$ is almost monotone, has a limit $\mu$, and a spectral-gap estimate for $-J_0\partial_t-S_\infty$ near $\mu$ upgrades the convergence to an exponential rate.
-- source:
--   Wendl, Lectures on Symplectic Field Theory (2026 notes), proof of Theorem 4.8.2 (linear asymptotic formula); U. Hryniewicz, J. Symplectic Geom. 12 (2014), proof of Theorem 2.11 (the step showing that $\alpha = F'/2F$ converges exponentially to an eigenvalue $\mu$, and the resulting $L^2$ bounds on $\eta = \partial_s\zeta - \mu\zeta$)

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open scoped ContDiff RealInnerProductSpace

/-- Stage of Wendl, Prop. 4.8.2 / Hryniewicz, Thm. 2.11: under the hypotheses of
`halfCyl_asymptotic_formula`, put `F(s) = ∫₀¹ |ζ(s,t)|² dt`, `α(s) = ⟨ζ, ∂ₛζ⟩_{L²} / F(s)` and
`q(s) = ‖∂ₛζ‖²_{L²} / F(s) - α(s)²`. Then `F > 0` for large `s`, `α` converges exponentially fast to
some `μ ≤ δ₀`, the tail integrals of `q` decay exponentially, `η = ∂ₛζ - μζ` satisfies
`‖η(s)‖²_{L²} ≤ K e^{-as} F(s)` and `‖∂ₛη(s)‖²_{L²} ≤ K F(s)`. -/
theorem halfCyl_alpha_eta_bounds {n : ℕ} (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) (hζ : IsHalfCylSolution S ζ)
    (hne : ∃ p : ℝ × ℝ, 0 < p.1 ∧ ζ p ≠ 0)
    (C δ₀ : ℝ) (hgrowth : ∀ s > 0, ∀ t : ℝ, ‖ζ (s, t)‖ ≤ C * Real.exp (δ₀ * s)) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ ∃ s₀ > 0, ∃ a > 0, ∃ K : ℝ, ∀ s ≥ s₀,
      0 < ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 ∧
      |(∫ t in (0:ℝ)..1, ⟪ζ (s, t), fderiv ℝ ζ (s, t) (1, 0)⟫) / (∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2)
        - μ| ≤ K * Real.exp (-(a * s)) ∧
      (∀ T ≥ s, ∫ x in s..T,
        ((∫ t in (0:ℝ)..1, ‖fderiv ℝ ζ (x, t) (1, 0)‖ ^ 2) / (∫ t in (0:ℝ)..1, ‖ζ (x, t)‖ ^ 2) -
          ((∫ t in (0:ℝ)..1, ⟪ζ (x, t), fderiv ℝ ζ (x, t) (1, 0)⟫) /
            (∫ t in (0:ℝ)..1, ‖ζ (x, t)‖ ^ 2)) ^ 2) ≤ K * Real.exp (-(a * s))) ∧
      ∫ t in (0:ℝ)..1, ‖fderiv ℝ ζ (s, t) (1, 0) - μ • ζ (s, t)‖ ^ 2 ≤
        K * Real.exp (-(a * s)) * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 ∧
      ∫ t in (0:ℝ)..1, ‖fderiv ℝ (fun p => fderiv ℝ ζ p (1, 0) - μ • ζ p) (s, t) (1, 0)‖ ^ 2 ≤
        K * ∫ t in (0:ℝ)..1, ‖ζ (s, t)‖ ^ 2 := by sorry

end FiniteEnergyPlane
