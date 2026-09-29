-- Prove2me | Theorems.Thm_BoltzmannConstant_ideal_gas_law_per_molecule
-- name    : BoltzmannConstant.ideal_gas_law_per_molecule
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T14:07:06.74478+00:00
-- url     : https://prove2.me/theorems/6161a231-99d9-4ad8-92db-185eae35e27b
-- title:
--   Per-molecule form of the ideal gas law, $pV = Nk_BT$
-- statement:
--   The ideal gas law in its molar form states that $pV = nRT$, where $n$ is the amount of substance and $R$ the molar gas constant. Introducing the Boltzmann constant as the gas constant per molecule, $k_B = R/N_A$, and writing $N = nN_A$ for the number of molecules, the molar law is *equivalent* to the per-molecule law $$pV = N k_B T.$$ This equivalence is the sense in which $k_B$ is "the gas constant per molecule".
-- source:
--   Wikipedia, "Boltzmann constant" (uploaded PDF), https://en.wikipedia.org/wiki/Boltzmann_constant, section "Roles of the Boltzmann constant" ($pV = nRT$, $k = R/N_A$, $pV = Nk T$)

import Mathlib
import Definitions.Def_boltzmann_si_basics

namespace BoltzmannConstant

theorem ideal_gas_law_per_molecule (n N p V T : ℝ) (hN : N = n * NA) :
    p * V = n * R * T ↔ p * V = N * kB * T := by sorry

end BoltzmannConstant
