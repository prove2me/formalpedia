-- Prove2me | Theorems.Thm_BlackbodyRadiation_wien_displacement_law_frequency
-- name    : BlackbodyRadiation.wien_displacement_law_frequency
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T18:39:40.732429+00:00
-- url     : https://prove2.me/theorems/6f306ff6-0089-4882-af05-9050651be573
-- title:
--   Wien's displacement law, frequency parameterization: $\nu_{\max}= (x_3 k_B/h)\,T$
-- statement:
--   For spectral radiance considered per unit **frequency**, Wien's displacement law states that
--   the emission peaks at a frequency directly proportional to the absolute temperature:
--
--   $$\nu_{\mathrm{peak}} \;=\; \frac{x_3 k_B}{h}\,T,
--   \qquad x_3 = 2.821\,439\,372\,122\,078\,893\ldots,$$
--
--   where $x_3$ is the positive root of the frequency maximization equation
--   $x = 3(1 - e^{-x})$. In SI units the proportionality constant is
--   $0.058\,789\,257\ldots\ \mathrm{THz\cdot K^{-1}}$.
--
--   The milestone asserts, for positive $h$, $c$, $k_B$, the existence of a positive constant
--   $a$ of exactly this form — $a = x k_B/h$ for a positive solution $x$ of
--   $x = 3(1 - e^{-x})$ — such that for every temperature $T > 0$ the function
--   $\nu \mapsto B_\nu(\nu, T)$ attains a strict global maximum on $(0,\infty)$ at $\nu = aT$,
--   and at no other frequency.
--
--   The constant differs from the wavelength one, and the corresponding peak wavelength
--   $c/\nu_{\mathrm{peak}}$ is about $76\%$ longer than the peak of the wavelength-parameterized
--   curve. This is not a contradiction but the Jacobian effect recorded in the first milestone.
-- source:
--   Wien's displacement law, Wikipedia, https://en.wikipedia.org/wiki/Wien%27s_displacement_law , section "Derivation from Planck's law / Parameterization by wavelength" and "Parameterization by frequency". — section "Frequency-dependent formulation" (nu_peak = (alpha k/h) T with alpha = 2.821439372122078893...) and section "Derivation from Planck's law / Parameterization by frequency".

import Mathlib
import Definitions.Def_BlackbodyRadiation_planck

namespace BlackbodyRadiation
theorem wien_displacement_law_frequency
    (h c kB : ℝ) (hh : 0 < h) (hc : 0 < c) (hkB : 0 < kB) :
    ∃ a : ℝ, 0 < a ∧
      (∃ x : ℝ, 0 < x ∧ x = 3 * (1 - Real.exp (-x)) ∧ a = x * kB / h) ∧
      ∀ T : ℝ, 0 < T → ∀ ν : ℝ, 0 < ν → ν ≠ a * T →
        planckFreq h c kB T ν < planckFreq h c kB T (a * T) := by sorry
end BlackbodyRadiation
