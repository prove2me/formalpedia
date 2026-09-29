-- Prove2me | Theorems.Thm_CODATA2022_stefanBoltzmannConstant_eq_planck_form
-- name    : CODATA2022.stefanBoltzmannConstant_eq_planck_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:12:11.863726+00:00
-- url     : https://prove2.me/theorems/01a9bb71-e1a9-48ba-90a7-97812263ad4c
-- title:
--   $\sigma = (\pi^2/60)k^4/\hbar^3c^2 = 2\pi^5k^4/(15h^3c^2)$
-- statement:
--   The tabulated closed form of the Stefan-Boltzmann constant, $\sigma = (\pi^2/60)k^4/\hbar^3c^2$, written in terms of $h$ rather than $\hbar = h/2\pi$:
--
--   $$\sigma \;=\; \frac{\pi^2}{60}\frac{k^4}{\hbar^3c^2} \;=\; \frac{2\pi^5k^4}{15\,h^3c^2}.$$
--
--   This is the form in which $\sigma$ emerges from integrating Planck's law, so the identity is the bridge between the goal theorem and the tabulated expression.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Table XXXII and Nomenclature entry for $\sigma$.

import Mathlib
import Definitions.Def_CODATA2022_si_defining_constants
import Definitions.Def_CODATA2022_radiation_constants
open MeasureTheory

namespace CODATA2022
theorem stefanBoltzmannConstant_eq_planck_form :
    stefanBoltzmannConstant
      = 2 * Real.pi ^ 5 * boltzmannConstant ^ 4 /
          (15 * planckConstant ^ 3 * speedOfLight ^ 2) := by sorry
end CODATA2022
