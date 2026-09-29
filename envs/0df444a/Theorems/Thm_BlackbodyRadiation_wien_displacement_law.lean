-- Prove2me | Theorems.Thm_BlackbodyRadiation_wien_displacement_law
-- name    : BlackbodyRadiation.wien_displacement_law
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T18:40:48.902974+00:00
-- url     : https://prove2.me/theorems/f740af08-ecf7-4a53-9489-df37948e4537
-- title:
--   Wien's displacement law: $\lambda_{\max}=b/T$ with $b=hc/(x_5k_B)$
-- statement:
--   **Wien's displacement law.** The black-body radiation curve for different temperatures
--   peaks at different wavelengths, inversely proportional to the temperature. Formally, the
--   spectral radiance of black-body radiation per unit wavelength peaks at
--
--   $$\lambda_{\mathrm{peak}} \;=\; \frac{b}{T},$$
--
--   where $T$ is the absolute temperature and $b$ is Wien's displacement constant. It is a
--   direct consequence of Planck's radiation law, and the derivation identifies $b$ explicitly:
--   differentiating
--
--   $$B_\lambda(\lambda, T) \;=\; \frac{2hc^{2}/\lambda^{5}}{\exp\!\bigl(hc/(\lambda k_B T)\bigr)-1}$$
--
--   with respect to $\lambda$ and setting the derivative to zero gives, in the variable
--   $x = hc/(\lambda k_B T)$, the equation $x = 5(1 - e^{-x})$, whose positive root is
--   $x_5 = 4.965114231744276303\ldots$; hence
--
--   $$b \;=\; \frac{hc}{x_5 k_B} \;=\; 2.897\,771\,955\ldots \times 10^{-3}\ \mathrm{m\cdot K}.$$
--
--   The goal theorem states this for arbitrary positive $h$, $c$, $k_B$: there is a constant
--   $b > 0$, of the form $hc/(xk_B)$ with $x$ a positive solution of $x = 5(1 - e^{-x})$, such
--   that for every temperature $T > 0$ the function $\lambda \mapsto B_\lambda(\lambda, T)$ has
--   a strict global maximum on $(0,\infty)$, attained at $\lambda = b/T$ and nowhere else.
--
--   Two design choices make the statement the strongest reasonable one. The maximum is stated
--   as a strict inequality against every other positive wavelength, so it excludes a merely
--   local peak or a stationary point that is not a maximum. And the same $b$ serves all
--   temperatures, which is precisely the inverse proportionality that the law asserts.
-- source:
--   Wien's displacement law, Wikipedia, https://en.wikipedia.org/wiki/Wien%27s_displacement_law , section "Derivation from Planck's law / Parameterization by wavelength" and "Parameterization by frequency". — the statement "the spectral radiance of black-body radiation per unit wavelength peaks at the wavelength lambda_peak = b/T" together with the section "Derivation from Planck's law / Parameterization by wavelength" giving x = 4.965114231744276303... and b = 2.897771955185172661 mm K; the underlying B_lambda is from Planck's law, Wikipedia, https://en.wikipedia.org/wiki/Planck%27s_law , sections "The law" (frequency form and wavelength form of the spectral radiance B_nu and B_lambda) and "Properties / Peaks"..

import Mathlib
import Definitions.Def_BlackbodyRadiation_planck

namespace BlackbodyRadiation
theorem wien_displacement_law
    (h c kB : ℝ) (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) :
    ∃ b : ℝ, 0 < b ∧
      (∃ x : ℝ, 0 < x ∧ x = 5 * (1 - Real.exp (-x)) ∧ b = h * c / (x * kB)) ∧
      ∀ T : ℝ, 0 < T → ∀ lam : ℝ, 0 < lam → lam ≠ b / T →
        planckWave h c kB T lam < planckWave h c kB T (b / T) := by sorry
end BlackbodyRadiation
