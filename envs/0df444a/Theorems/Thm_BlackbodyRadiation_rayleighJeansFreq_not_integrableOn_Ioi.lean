-- Prove2me | Theorems.Thm_BlackbodyRadiation_rayleighJeansFreq_not_integrableOn_Ioi
-- name    : BlackbodyRadiation.rayleighJeansFreq_not_integrableOn_Ioi
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T14:03:48.591467+00:00
-- url     : https://prove2.me/theorems/80dc6237-cfe1-4987-9b5b-228619e83b49
-- title:
--   Ultraviolet catastrophe: $B^{\mathrm{RJ}}_\nu$ is not integrable on $(0,\infty)$
-- statement:
--   **The ultraviolet catastrophe, stated exactly.** For positive $c$, $k_B$ and $T$, the
--   Rayleigh-Jeans spectral radiance $B^{\mathrm{RJ}}_\nu(\nu,T) = 2\nu^2k_BT/c^2$ is not
--   Lebesgue integrable on $(0,\infty)$: a classical black body with equipartitioned modes
--   would radiate infinite total power. The statement is the negation of integrability, which
--   is stronger and cleaner than saying that the improper integral diverges: it rules out any
--   finite value for the total emission, not merely the convergence of one particular
--   exhaustion.
-- source:
--   Planck constant, Wikipedia, https://en.wikipedia.org/wiki/Planck_constant , section "History", subsections "Origin of the constant" (Wien's law at short wavelengths, the Rayleigh-Jeans formula at long wavelengths, and Planck's spectral radiance per unit frequency) and "Development and application" (the ultraviolet catastrophe).

import Mathlib
import Definitions.Def_BlackbodyRadiation_planck
import Definitions.Def_BlackbodyRadiation_classical_limits
open MeasureTheory

namespace BlackbodyRadiation
theorem rayleighJeansFreq_not_integrableOn_Ioi
    (c kB T : ℝ) (hc : 0 < c) (hkB : 0 < kB) (hT : 0 < T) :
    ¬ IntegrableOn (fun ν : ℝ => rayleighJeansFreq c kB T ν) (Set.Ioi 0) volume := by sorry
end BlackbodyRadiation
