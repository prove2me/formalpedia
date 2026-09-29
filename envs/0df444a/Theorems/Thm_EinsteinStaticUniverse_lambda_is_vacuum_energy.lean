-- Prove2me | Theorems.Thm_EinsteinStaticUniverse_lambda_is_vacuum_energy
-- name    : EinsteinStaticUniverse.lambda_is_vacuum_energy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T04:21:08.886164+00:00
-- url     : https://prove2.me/theorems/6d559b35-0295-4a9f-aeda-ed7d4e894fcc
-- title:
--   $\Lambda$ is a perfect fluid with $\rho_{\mathrm{vac}}=\Lambda/8\pi G$ and $w=-1$
-- statement:
--   A cosmological constant is indistinguishable, at the level of the Friedmann equations, from a perfect fluid of constant energy density and negative pressure. Let $G\neq0$ and let $\Lambda,k$ be real, let $\rho$ be any energy-density history, $a$ any scale factor and $I$ any set of times. Then the first Friedmann equation with cosmological constant $\Lambda$,
--   $$\dot a^{2}=\frac{8\pi G}{3}\rho\,a^{2}-k+\frac{\Lambda}{3}a^{2},$$
--   holds on $I$ if and only if the same equation **with $\Lambda$ removed** holds on $I$ for the shifted density $\rho+\rho_{\text{vac}}$, where
--   $$\rho_{\text{vac}}=\frac{\Lambda}{8\pi G},$$
--   i.e. $\Lambda=\kappa\rho_{\text{vac}}$ with $\kappa=8\pi G$. Moreover the pair $(\rho_{\text{vac}},p_{\text{vac}})$ with $p_{\text{vac}}=-\rho_{\text{vac}}$ satisfies the continuity equation
--   $$\dot\rho_{\text{vac}}+3\frac{\dot a}{a}\left(\rho_{\text{vac}}+p_{\text{vac}}\right)=0$$
--   for every scale factor $a$, which is the statement that a constant vacuum density is conserved precisely because its equation of state is $w=-1$.
--
--   This is the formal content of the standard move of shifting $\Lambda g_{\mu\nu}$ to the right-hand side of the field equations and calling it vacuum energy; it is the identification on which the cosmological constant problem rests.
-- source:
--   Wikipedia, 'Cosmological constant', https://en.wikipedia.org/wiki/Cosmological_constant (sections 'History', 'Equation', 'Density parameter', 'Equation of state', 'Value', 'Predictions'); Wikipedia, 'Cosmological constant problem', https://en.wikipedia.org/wiki/Cosmological_constant_problem (sections 'History', 'Estimated values')

import Mathlib
import Definitions.Def_EinsteinStaticUniverse_model

namespace EinsteinStaticUniverse

theorem lambda_is_vacuum_energy (G Λ k : ℝ) (hG : G ≠ 0) (ρ : ℝ → ℝ) (a : ℝ → ℝ) (I : Set ℝ) :
    (FriedmannGeneral G Λ k ρ a I ↔
      FriedmannGeneral G 0 k (fun t => ρ t + vacuumDensity G Λ) a I) ∧
    ContinuityEquation (fun _ => vacuumDensity G Λ) (fun _ => vacuumPressure G Λ) a I := by sorry

end EinsteinStaticUniverse
