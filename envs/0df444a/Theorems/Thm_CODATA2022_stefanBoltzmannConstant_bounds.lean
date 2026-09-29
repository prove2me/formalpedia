-- Prove2me | Theorems.Thm_CODATA2022_stefanBoltzmannConstant_bounds
-- name    : CODATA2022.stefanBoltzmannConstant_bounds
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:12:47.877893+00:00
-- url     : https://prove2.me/theorems/76d96925-75ae-4a68-aee3-0905089f919a
-- title:
--   Numerical enclosure $5.670\,374\,419\times10^{-8} < \sigma < 5.670\,374\,420\times10^{-8}$
-- statement:
--   CODATA 2022 lists the Stefan-Boltzmann constant as
--   $\sigma = 5.670\,374\,419\ldots\times10^{-8}\ \mathrm{W\,m^{-2}K^{-4}}$, exactly known but
--   irrational. This milestone certifies the tabulated digits:
--
--   $$5.670\,374\,419\times10^{-8} \;<\; \sigma \;<\; 5.670\,374\,420\times10^{-8}.$$
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Table XXXIII, Physicochemical constants: Stefan-Boltzmann constant $5.670\,374\,419\ldots\times10^{-8}$.

import Mathlib
import Definitions.Def_CODATA2022_si_defining_constants
import Definitions.Def_CODATA2022_radiation_constants
open MeasureTheory

namespace CODATA2022
theorem stefanBoltzmannConstant_bounds :
    5.670374419e-8 < stefanBoltzmannConstant ∧ stefanBoltzmannConstant < 5.670374420e-8 := by
  sorry
end CODATA2022
