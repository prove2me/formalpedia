-- Prove2me | Theorems.Thm_EinsteinStaticUniverse_einstein_static_universe_exists_and_is_unstable
-- name    : EinsteinStaticUniverse.einstein_static_universe_exists_and_is_unstable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:27:04.028978+00:00
-- url     : https://prove2.me/theorems/3b6baacc-7f2c-4eb3-81b9-b0267147559f
-- title:
--   Einstein's static universe exists for exactly one balance of $\Lambda$, $\rho$ and $k$, and it is unstable
-- statement:
--   **Goal theorem of the mission.** Let $G,\rho_0,a_0,a_E$ be positive, let $\Lambda,k$ be arbitrary real parameters, and write $\rho_E=\rho_0(a_0/a_E)^{3}$ for the dust density at scale factor $a_E$ and
--   $$F(x)=-\frac{4\pi G}{3}\rho_0\left(\frac{a_0}{x}\right)^{3}x+\frac{\Lambda}{3}x$$
--   for the right-hand side of the acceleration equation. The theorem has two parts.
--
--   **Existence and uniqueness of the balance.** The constant scale factor $a\equiv a_E$ satisfies both Friedmann equations at all times if and only if
--   $$\Lambda=4\pi G\rho_E\qquad\text{and}\qquad k=\Lambda a_E^{2}.$$
--
--   **Instability.** Assume that balance, $\Lambda=4\pi G\rho_E$. Then $\Lambda>0$, the equilibrium is linearly repelling in the precise sense that $F$ is differentiable at $a_E$ with
--   $$F'(a_E)=\Lambda>0,$$
--   and the exact solutions behave accordingly:
--
--   1. every twice differentiable $a$ solving $\ddot a=F(a)$ on $[0,\infty)$ with $a(0)>a_E$ and $\dot a(0)\ge0$ is strictly increasing on $[0,\infty)$ and satisfies $a(t)\to\infty$;
--   2. for every $T>0$, every twice differentiable $a$ solving $\ddot a=F(a)$ on $[0,T]$, positive there, with $a(0)<a_E$ and $\dot a(0)\le0$, is strictly decreasing on $[0,T]$.
--
--   Thus Einstein's static universe exists for exactly one tuning of $\Lambda$ and $k$ against the matter density, and that equilibrium is unstable in both directions: an outward perturbation expands forever, an inward one collapses. This is the mathematical reason the static model was abandoned, and the $e$-folding rate $\sqrt{\Lambda}$ of the growing mode is the same exponential that reappears as the late-time de Sitter expansion of the standard cosmological model.
-- source:
--   Wikipedia, 'Cosmological constant', https://en.wikipedia.org/wiki/Cosmological_constant (sections 'History', 'Equation', 'Density parameter', 'Equation of state', 'Value', 'Predictions'); Wikipedia, 'Cosmological constant problem', https://en.wikipedia.org/wiki/Cosmological_constant_problem (sections 'History', 'Estimated values')

import Mathlib
import Definitions.Def_EinsteinStaticUniverse_model

namespace EinsteinStaticUniverse

theorem einstein_static_universe_exists_and_is_unstable (G Λ k ρ₀ a₀ aE : ℝ) (hG : 0 < G)
    (hρ₀ : 0 < ρ₀) (ha₀ : 0 < a₀) (haE : 0 < aE) :
    ((FriedmannI G Λ k ρ₀ a₀ (fun _ => aE) Set.univ ∧
        FriedmannII G Λ ρ₀ a₀ (fun _ => aE) Set.univ) ↔
      (Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE ∧ k = Λ * aE ^ 2)) ∧
    (Λ = 4 * Real.pi * G * dustDensity ρ₀ a₀ aE →
      0 < Λ ∧ HasDerivAt (accel G Λ ρ₀ a₀) Λ aE ∧
      (∀ a : ℝ → ℝ, (∀ t : ℝ, DifferentiableAt ℝ a t) →
        (∀ t : ℝ, DifferentiableAt ℝ (deriv a) t) →
        FriedmannII G Λ ρ₀ a₀ a (Set.Ici 0) → aE < a 0 → 0 ≤ deriv a 0 →
        StrictMonoOn a (Set.Ici 0) ∧ Filter.Tendsto a Filter.atTop Filter.atTop) ∧
      (∀ T : ℝ, 0 < T → ∀ a : ℝ → ℝ, (∀ t : ℝ, DifferentiableAt ℝ a t) →
        (∀ t : ℝ, DifferentiableAt ℝ (deriv a) t) →
        (∀ t ∈ Set.Icc 0 T, 0 < a t) → FriedmannII G Λ ρ₀ a₀ a (Set.Icc 0 T) →
        a 0 < aE → deriv a 0 ≤ 0 → StrictAntiOn a (Set.Icc 0 T))) := by sorry

end EinsteinStaticUniverse
