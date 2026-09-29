-- Prove2me | Theorems.Thm_BlackbodyRadiation_planckWave_eq_shape
-- name    : BlackbodyRadiation.planckWave_eq_shape
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T18:37:37.445837+00:00
-- url     : https://prove2.me/theorems/2bba2f77-79b0-4455-8fc9-1ecebffb5c52
-- title:
--   Strong form of Wien's law: the wavelength spectrum is a temperature-independent shape
-- statement:
--   Wien's displacement law in its **strong form** states that the shape of the Planck spectrum
--   is independent of temperature: changing $T$ rescales the curve, horizontally and vertically,
--   but does not deform it. This milestone is that statement, made explicit.
--
--   Introduce the dimensionless variable
--
--   $$x \;=\; \frac{hc}{\lambda k_B T}.$$
--
--   Then for all positive $h$, $c$, $k_B$, $T$, $\lambda$,
--
--   $$B_\lambda(\lambda, T) \;=\; \frac{2k_B^{5}T^{5}}{h^{4}c^{3}}\cdot g_5(x),
--   \qquad g_5(x) = \frac{x^{5}}{e^{x}-1}.$$
--
--   The prefactor depends on the temperature but not on the wavelength, and the shape function
--   $g_5$ depends on neither: all the $\lambda$-dependence has been absorbed into $x$. Locating
--   the peak of $B_\lambda$ therefore reduces, once and for all, to locating the maximum of a
--   single fixed function of one variable — which is how the peak wavelength is forced to be
--   inversely proportional to $T$, and how the percentile table of the black-body spectrum can
--   be tabulated once in the variable $\lambda T$.
-- source:
--   Wien's displacement law, Wikipedia, https://en.wikipedia.org/wiki/Wien%27s_displacement_law , section "Derivation from Planck's law / Parameterization by wavelength" and "Parameterization by frequency". — the reduction of the maximization to the single variable x = hc/(lambda k_B T); and Planck's law, Wikipedia, https://en.wikipedia.org/wiki/Planck%27s_law , sections "The law" (frequency form and wavelength form of the spectral radiance B_nu and B_lambda) and "Properties / Peaks". section "Percentiles" ("Wien's displacement law in its stronger form states that the shape of Planck's law is independent of temperature").

import Mathlib
import Definitions.Def_BlackbodyRadiation_planck

namespace BlackbodyRadiation
theorem planckWave_eq_shape
    (h c kB T lam : ℝ) (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) (hT : 0 < T)
    (hlam : 0 < lam) :
    planckWave h c kB T lam
      = 2 * kB ^ 5 * T ^ 5 / (h ^ 4 * c ^ 3) *
          planckShape 5 (h * c / (lam * kB * T)) := by sorry
end BlackbodyRadiation
