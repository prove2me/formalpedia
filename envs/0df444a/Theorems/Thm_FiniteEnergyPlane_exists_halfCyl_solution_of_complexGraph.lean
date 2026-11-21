-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_halfCyl_solution_of_complexGraph
-- name    : FiniteEnergyPlane.exists_halfCyl_solution_of_complexGraph
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T22:23:05.044038+00:00
-- url     : https://prove2.me/theorems/44321807-62bc-42d0-b469-68ce304b2f82
-- title:
--   The vertical difference of two complex graphs in a standard tube solves a Cauchy-Riemann type equation
-- statement:
--   Let $(\bar J, J_\infty, S_\infty)$ be a standard tube structure of radius $\rho$ and rate $b > 0$, and $\delta < 0$. Let $g : \mathbb{C} \to B_\rho(0)$ be smooth with $\bar J$-complex graph and $g(e^{2\pi(s+it)})$ decaying like $e^{\delta s}$ in $C^\infty$; let $\psi, v : \mathbb{C} \to \mathbb{C}$ be smooth, $v$ valued in $B_\rho(0)$, with $z \mapsto (\psi(z), v(z))$ $\bar J$-holomorphic, $\psi(z)/z - \kappa$ decaying like $e^{-b's}$ ($\kappa \ne 0$, $b' > 0$) and $v(e^{2\pi(s+it)})$ decaying like $e^{\delta s}$, all in $C^\infty$. Then there are a smooth family of injective real-linear maps $P(z) : \mathbb{C} \to \mathbb{C}$, a smooth $1$-periodic matrix function $S(s,t)$, a function $w$ and constants $d > 0$, $C$ such that, for $\zeta(z) = P(z)(v(z) - g(\psi(z)))$:
--   - $\zeta$ is smooth and satisfies locally $|\partial_x \zeta + i\, \partial_y \zeta| \le M |\zeta|$;
--   - $S(s,t) - S_\infty(t + \arg\kappa / 2\pi)$ decays like $e^{-ds}$ in $C^\infty$;
--   - $w$ solves $\partial_s w + J_0 \partial_t w + S w = 0$ on the half-cylinder $s > 0$;
--   - $w(s,t) = \zeta(e^{2\pi(s+it)})$ and $|w(s,t)| \le C e^{\delta s}$ for $s > 0$.
--
--   Role: the vertical difference between a holomorphic graph and a $\bar J$-complex graph in a standard tube satisfies a linear Cauchy-Riemann type equation, both locally and on the cylindrical end, with an asymptotic operator conjugate to the one of the tube.
--
--   Formalization Note: $e^{2\pi(s+it)}$ is `cylInf s t`; decay is `ExpDecayCInfty` and `IsExpAsymptoticTo`; the equation is `IsHalfCylSolution S w`; $w$ takes values in `Vec 1` and is compared with $\zeta$ through `vecToC`.
-- source:
--   Standard tube structures in the theory of fast finite-energy planes; U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_Tube

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The vertical difference `v z - g (ψ z)` between a holomorphic graph `z ↦ (ψ z, v z)` of a
standard tube structure and a `Jbar`-complex graph `x ↦ (x, g x)`, both decaying like `e^{δ s}`,
`δ < 0`, written in a smooth pointwise injective real-linear frame `P`, satisfies
`|∂ₛζ + i ∂ₜζ| ≤ M |ζ|` locally, and in the cylindrical coordinates at `∞` it is a solution `w` of
`∂ₛw + J₀ ∂ₜw + S w = 0` on `s > 0` with `‖w‖ ≤ C e^{δ s}`, where `S - S∞(· + arg κ / 2π)` decays
exponentially in `C^∞`. -/
theorem exists_halfCyl_solution_of_complexGraph (ρ b : ℝ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0)
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgρ : ∀ x, g x ∈ ball (0 : ℂ) ρ)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1)
    (hgas : ExpDecayCInfty (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) (-δ))
    (ψ v : ℂ → ℂ) (κ : ℂ) (b' : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v) (hvρ : ∀ z, v z ∈ ball (0 : ℂ) ρ)
    (hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z))
    (hκ : κ ≠ 0) (hb' : 0 < b')
    (hψas : ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b')
    (hvas : ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ)) :
    ∃ (P : ℂ → ℂ →L[ℝ] ℂ) (S : ℝ × ℝ → CauchyRiemannIndex.Mat 1)
      (w : ℝ × ℝ → CauchyRiemannIndex.Vec 1) (d C : ℝ),
      (∀ z, Function.Injective (P z)) ∧
      ContDiff ℝ ∞ (fun z => P z (v z - g (ψ z))) ∧
      (∀ z₀ : ℂ, ∃ r > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ r,
        ‖fderiv ℝ (fun y => P y (v y - g (ψ y))) z 1 +
            Complex.I * fderiv ℝ (fun y => P y (v y - g (ψ y))) z Complex.I‖ ≤
          M * ‖P z (v z - g (ψ z))‖) ∧
      (∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p i j)) ∧
      (∀ s t : ℝ, S (s, t + 1) = S (s, t)) ∧
      0 < d ∧ IsExpAsymptoticTo S (fun t => Sinf (t + Complex.arg κ / (2 * π))) d ∧
      IsHalfCylSolution S w ∧
      (∀ s > 0, ∀ t : ℝ, vecToC (w (s, t)) = P (cylInf s t) (v (cylInf s t) - g (ψ (cylInf s t)))) ∧
      ∀ s > 0, ∀ t : ℝ, ‖w (s, t)‖ ≤ C * Real.exp (δ * s) := by
  sorry

end FiniteEnergyPlane
