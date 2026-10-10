-- Prove2me | Theorems.Thm_CosmologyEOS_perfect_gas_eos_parameter
-- name    : CosmologyEOS.perfect_gas_eos_parameter
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:30.932633+00:00
-- url     : https://prove2.me/theorems/f3503903-66d1-4f50-b4ef-618ded628cc6
-- title:
--   Perfect gas: $w = c_s^2/c^2$
-- statement:
--   Consider a perfect gas with mass density $\rho\neq 0$, particular gas constant $R$ and temperature $T$ with $RT\ge 0$, and let $c\neq0$ be the speed of light. Its pressure is $p = \rho R T = \rho c_s^2$ with thermal speed $c_s = \sqrt{RT}$, and its energy density is $\varepsilon = \rho c^2$. Then both expressions of the pressure give
--
--   $$w = \frac{p}{\varepsilon} = \frac{\rho R T}{\rho c^2} = \frac{\rho c_s^2}{\rho c^2} = \frac{c_s^2}{c^2}.$$
--
--   This is the identity behind the statement that a cold gas ($c_s \ll c$) has $w \approx 0$.
--
--   **Formalization Note** The approximation $w\approx 0$ is not formalized; only the exact identity is.
-- source:
--   Wikipedia, "Equation of state (cosmology)", revision 1375011367, https://en.wikipedia.org/w/index.php?title=Equation_of_state_(cosmology)&oldid=1375011367, section 'The equation'

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology

namespace CosmologyEOS

theorem perfect_gas_eos_parameter (ρ R T c : ℝ) (hρ : ρ ≠ 0) (hc : c ≠ 0)
    (hRT : 0 ≤ R * T) :
    eosParameter (ρ * R * T) (ρ * c ^ 2) = (Real.sqrt (R * T)) ^ 2 / c ^ 2 ∧
      eosParameter (ρ * (Real.sqrt (R * T)) ^ 2) (ρ * c ^ 2) = (Real.sqrt (R * T)) ^ 2 / c ^ 2 := by
  sorry

end CosmologyEOS
