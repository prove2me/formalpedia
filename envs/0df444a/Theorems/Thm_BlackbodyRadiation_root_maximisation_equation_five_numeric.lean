-- Prove2me | Theorems.Thm_BlackbodyRadiation_root_maximisation_equation_five_numeric
-- name    : BlackbodyRadiation.root_maximisation_equation_five_numeric
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T18:40:08.280984+00:00
-- url     : https://prove2.me/theorems/394453df-c59b-468f-b883-13990a3fbf40
-- title:
--   Numerical enclosure of the Wien constant root $x_5=4.965114231744276303\ldots$
-- statement:
--   The wavelength form of Wien's displacement law reads $\lambda_{\mathrm{peak}} = b/T$ with
--
--   $$b \;=\; \frac{hc}{x_5 k_B},$$
--
--   so the numerical value of Wien's displacement constant,
--   $b = 2.897\,771\,955\,185\,172\,661\ldots \times 10^{-3}\ \mathrm{m\cdot K}$, is entirely
--   determined by the root
--
--   $$x_5 \;=\; 4.965\,114\,231\,744\,276\,303\ldots$$
--
--   of the maximization equation $x = 5(1 - e^{-x})$.
--
--   This milestone certifies that value to ten decimal places: any positive solution $x$ of
--   $x = 5(1 - e^{-x})$ satisfies
--
--   $$4.9651142317 \;<\; x \;<\; 4.9651142318.$$
--
--   Combined with the uniqueness milestone, this pins the constant down rather than merely
--   asserting that some constant exists. A rigorous proof needs certified bounds on the
--   exponential at a specific rational point; floating-point evaluation does not suffice.
-- source:
--   Wien's displacement law, Wikipedia, https://en.wikipedia.org/wiki/Wien%27s_displacement_law , section "Derivation from Planck's law / Parameterization by wavelength" and "Parameterization by frequency". — "gives x = 4.965114231744276303..." and the resulting b = 2.897771955185172661 mm K.

import Mathlib
import Definitions.Def_BlackbodyRadiation_planck

namespace BlackbodyRadiation
theorem root_maximisation_equation_five_numeric
    (x : ℝ) (hx : 0 < x) (hroot : x = 5 * (1 - Real.exp (-x))) :
    4.9651142317 < x ∧ x < 4.9651142318 := by sorry
end BlackbodyRadiation
