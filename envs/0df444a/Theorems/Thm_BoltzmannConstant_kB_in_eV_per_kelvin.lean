-- Prove2me | Theorems.Thm_BoltzmannConstant_kB_in_eV_per_kelvin
-- name    : BoltzmannConstant.kB_in_eV_per_kelvin
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T15:34:55.814511+00:00
-- url     : https://prove2.me/theorems/e0c8bace-ae3e-4f4e-b5ed-0e26f2be6f39
-- title:
--   $k_B \approx 8.617333262\times10^{-5}$ eV/K
-- statement:
--   Since $k_B$ is a proportionality constant between temperature and energy, its numerical value depends on the energy unit. Expressed in electronvolts per kelvin — that is, dividing the value in J/K by the elementary charge in coulombs — it equals $8.617333262\ldots\times10^{-5}\ \mathrm{eV\,K^{-1}}$. The claim bounds the deviation of $k_B/q$ from the tabulated ten-digit value by $10^{-13}$.
-- source:
--   Wikipedia, "Boltzmann constant" (uploaded PDF), https://en.wikipedia.org/wiki/Boltzmann_constant, infobox "Value in electronvolts per kelvin" and section "Value in different units" ($8.617\,333\,262\ldots \times 10^{-5}$ eV/K)

import Mathlib
import Definitions.Def_boltzmann_si_basics

namespace BoltzmannConstant

theorem kB_in_eV_per_kelvin : |kB / elemCharge - 8.617333262e-5| < 1e-13 := by sorry

end BoltzmannConstant
