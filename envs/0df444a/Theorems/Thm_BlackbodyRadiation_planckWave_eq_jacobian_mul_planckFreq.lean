-- Prove2me | Theorems.Thm_BlackbodyRadiation_planckWave_eq_jacobian_mul_planckFreq
-- name    : BlackbodyRadiation.planckWave_eq_jacobian_mul_planckFreq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T18:36:26.563662+00:00
-- url     : https://prove2.me/theorems/9e40a2ee-04d5-4d62-96a3-a7650ddad9dd
-- title:
--   Wavelength and frequency forms of Planck's law differ by the Jacobian $c/\lambda^2$
-- statement:
--   Planck's law has a frequency form $B_\nu$ and a wavelength form $B_\lambda$, and they are
--   different functions. Because a spectral radiance is a density — radiance per increment of
--   its own spectral variable — one cannot pass from one to the other by the substitution
--   $\nu = c/\lambda$ alone; the Jacobian of the change of variable must be included.
--
--   This milestone records the exact relation. For positive $c$ and positive $\lambda$, and for
--   arbitrary $h$, $k_B$, $T$,
--
--   $$B_\lambda(\lambda, T) \;=\; \frac{c}{\lambda^{2}}\; B_\nu\!\left(\frac{c}{\lambda},\, T\right),$$
--
--   the factor $c/\lambda^{2}$ being $\left|\dfrac{d\nu}{d\lambda}\right|$ at $\nu = c/\lambda$.
--   It is this factor that shifts the peak of the distribution, so that the wavelength curve and
--   the frequency curve, at the same temperature, attain their maxima at physically different
--   places.
-- source:
--   Planck's law, Wikipedia, https://en.wikipedia.org/wiki/Planck%27s_law , sections "The law" (frequency form and wavelength form of the spectral radiance B_nu and B_lambda) and "Properties / Peaks". — the remark that one cannot pass from B_nu to B_lambda by substituting nu by lambda, but must also multiply by the Jacobian; see also Wien's displacement law, Wikipedia, https://en.wikipedia.org/wiki/Wien%27s_displacement_law , section "Derivation from Planck's law / Parameterization by wavelength" and "Parameterization by frequency". section "Parameterization by wavelength".

import Mathlib
import Definitions.Def_BlackbodyRadiation_planck

namespace BlackbodyRadiation
theorem planckWave_eq_jacobian_mul_planckFreq
    (h c kB T lam : ℝ) (hc : 0 < c) (hlam : 0 < lam) :
    planckWave h c kB T lam = c / lam ^ 2 * planckFreq h c kB T (c / lam) := by sorry
end BlackbodyRadiation
