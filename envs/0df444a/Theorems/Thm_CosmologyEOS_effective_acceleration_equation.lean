-- Prove2me | Theorems.Thm_CosmologyEOS_effective_acceleration_equation
-- name    : CosmologyEOS.effective_acceleration_equation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:39.306224+00:00
-- url     : https://prove2.me/theorems/f9489f0e-3eb5-4a7a-9cc1-c9e0d4267305
-- title:
--   Acceleration equation in effective variables
-- statement:
--   Let $G\neq 0$ and $\Lambda$ be real, and let $a,\varepsilon,p$ be real functions of time. Define the effective energy density and pressure $\varepsilon' = \varepsilon + \frac{\Lambda}{8\pi G}$ and $p' = p - \frac{\Lambda}{8\pi G}$. Then at every time $t$:
--
--   1. the acceleration equation $3\frac{\ddot a}{a} = \Lambda - 4\pi G(\varepsilon + 3p)$ holds if and only if
--   $$\frac{\ddot a}{a} = -\frac43\pi G\,(\varepsilon' + 3p');$$
--   2. if $\varepsilon'\neq 0$ and $w' = p'/\varepsilon'$, then
--   $$-\frac43\pi G\,(\varepsilon'+3p') = -\frac43\pi G\,(1+3w')\,\varepsilon'.$$
--
--   This expresses the effect of the cosmological constant as a shift of the fluid variables.
--
--   **Formalization Note** No sign or regularity hypotheses are needed: the statement is an identity between the two forms of the equation at a single time.
-- source:
--   Wikipedia, "Equation of state (cosmology)", revision 1375011367, https://en.wikipedia.org/w/index.php?title=Equation_of_state_(cosmology)&oldid=1375011367, section 'FLRW equations and the equation of state' (Friedmann acceleration equation, effective ε', p', w')

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology

namespace CosmologyEOS

theorem effective_acceleration_equation (G Λ : ℝ) (hG : G ≠ 0) (a ε p : ℝ → ℝ) (t : ℝ) :
    (AccelerationEquation G Λ a ε p t ↔
      deriv (deriv a) t / a t =
        -(4 / 3) * π * G *
          (effectiveEnergyDensity G Λ (ε t) + 3 * effectivePressure G Λ (p t))) ∧
    (effectiveEnergyDensity G Λ (ε t) ≠ 0 →
      -(4 / 3) * π * G *
          (effectiveEnergyDensity G Λ (ε t) + 3 * effectivePressure G Λ (p t)) =
        -(4 / 3) * π * G *
          (1 + 3 * eosParameter (effectivePressure G Λ (p t)) (effectiveEnergyDensity G Λ (ε t))) *
          effectiveEnergyDensity G Λ (ε t)) := by
  sorry

end CosmologyEOS
