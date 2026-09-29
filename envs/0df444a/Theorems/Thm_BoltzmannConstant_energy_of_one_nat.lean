-- Prove2me | Theorems.Thm_BoltzmannConstant_energy_of_one_nat
-- name    : BoltzmannConstant.energy_of_one_nat
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T14:46:17.937983+00:00
-- url     : https://prove2.me/theorems/140be735-1507-44e8-93bb-06167090310b
-- title:
--   $k_BT$ is the energy of one nat of rescaled entropy
-- statement:
--   The characteristic energy $k_BT$ has a direct information-theoretic reading: it is the energy required to increase the rescaled entropy $S/k_B$ by one nat. If two states of a system at temperature $T$ have rescaled entropies differing by exactly $1$, then the associated energy $T\,\Delta S$ equals $k_BT$.
-- source:
--   Wikipedia, "Boltzmann constant" (uploaded PDF), https://en.wikipedia.org/wiki/Boltzmann_constant, section "Role in the statistical definition of entropy" ("The characteristic energy $kT$ is thus the energy required to increase the rescaled entropy by one nat")

import Mathlib
import Definitions.Def_boltzmann_si_basics

namespace BoltzmannConstant

theorem energy_of_one_nat (T S₁ S₂ : ℝ) (h : S₂ / kB = S₁ / kB + 1) :
    T * (S₂ - S₁) = kB * T := by sorry

end BoltzmannConstant
