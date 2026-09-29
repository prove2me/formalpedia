-- Prove2me | Theorems.Thm_BlackbodyRadiation_planckFreq_div_rayleighJeansFreq_tendsto_one
-- name    : BlackbodyRadiation.planckFreq_div_rayleighJeansFreq_tendsto_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T13:53:00.482362+00:00
-- url     : https://prove2.me/theorems/41710471-8088-4dfc-b230-0c693d7646f9
-- title:
--   Rayleigh--Jeans long-wavelength limit: $B_\nu/B^{\mathrm{RJ}}_\nu\to1$ as $\nu\to0^+$
-- statement:
--   **Planck's law degenerates to the Rayleigh-Jeans law at low frequency.** For positive
--   $h$, $c$, $k_B$ and $T$, the ratio of the Planck spectral radiance to the classical
--   Rayleigh-Jeans radiance,
--
--   $$\frac{B_\nu(\nu,T)}{B^{\mathrm{RJ}}_\nu(\nu,T)}
--   = \frac{2h\nu^3/c^2}{\exp\!\left(\frac{h\nu}{k_BT}\right)-1}\cdot\frac{c^2}{2\nu^2k_BT}
--   = \frac{x}{e^{x}-1}, \qquad x = \frac{h\nu}{k_BT},$$
--
--   tends to $1$ as $\nu \to 0^+$. This is the precise form of the statement that Planck's
--   formula reproduces the empirical long-wavelength law that classical equipartition
--   predicts, and it is one of the two fitting constraints Planck imposed on his expression.
--   The comparison is made as a ratio, not as a difference: both radiances vanish at $\nu=0$,
--   so a difference tending to $0$ would be a strictly weaker claim.
-- source:
--   Planck constant, Wikipedia, https://en.wikipedia.org/wiki/Planck_constant , section "History", subsections "Origin of the constant" (Wien's law at short wavelengths, the Rayleigh-Jeans formula at long wavelengths, and Planck's spectral radiance per unit frequency) and "Development and application" (the ultraviolet catastrophe).

import Mathlib
import Definitions.Def_BlackbodyRadiation_planck
import Definitions.Def_BlackbodyRadiation_classical_limits
open MeasureTheory

namespace BlackbodyRadiation
theorem planckFreq_div_rayleighJeansFreq_tendsto_one
    (h c kB T : ℝ) (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) (hT : 0 < T) :
    Filter.Tendsto (fun ν : ℝ => planckFreq h c kB T ν / rayleighJeansFreq c kB T ν)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by sorry
end BlackbodyRadiation
