-- Prove2me | Theorems.Thm_BlackbodyRadiation_planckShape_lt_planckShape_of_root
-- name    : BlackbodyRadiation.planckShape_lt_planckShape_of_root
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T18:39:10.929455+00:00
-- url     : https://prove2.me/theorems/1b54f449-028e-4551-b646-ba2df32a4ce3
-- title:
--   The shape function $x^n/(e^x-1)$ has a strict global maximum at the root of $x=n(1-e^{-x})$
-- statement:
--   This is the analytic heart of the derivation. Once the Planck spectrum has been reduced to
--   the shape function
--
--   $$g_n(x) \;=\; \frac{x^{n}}{e^{x}-1}, \qquad x > 0,$$
--
--   locating the peak of the spectrum means locating the maximum of $g_n$.
--
--   The milestone asserts that for every integer $n \ge 2$, if $x_0 > 0$ solves the maximization
--   equation $x_0 = n(1 - e^{-x_0})$, then $x_0$ is a **strict global maximizer** of $g_n$ on
--   $(0, \infty)$: for every other positive $x$,
--
--   $$g_n(x) \;<\; g_n(x_0).$$
--
--   The strict global form matters. Setting the derivative to zero only produces a critical
--   point; by itself that does not exclude a minimum, an inflection, or a second competing peak
--   further out. Since $g_n$ has no closed-form maximizer, the global statement must be obtained
--   from the behaviour of $g_n$ on the whole half-line — it tends to $0$ at both ends and is
--   positive in between — rather than from a local second-derivative test.
--
--   Applied with $n = 5$ and $n = 3$, this milestone yields the wavelength and frequency
--   versions of Wien's displacement law.
-- source:
--   Wien's displacement law, Wikipedia, https://en.wikipedia.org/wiki/Wien%27s_displacement_law , section "Derivation from Planck's law / Parameterization by wavelength" and "Parameterization by frequency". — the step "Differentiating B_lambda with respect to lambda and setting the derivative equal to zero" reduced to the single variable x, together with Planck's law, Wikipedia, https://en.wikipedia.org/wiki/Planck%27s_law , sections "The law" (frequency form and wavelength form of the spectral radiance B_nu and B_lambda) and "Properties / Peaks". section "Properties / Peaks".

import Mathlib
import Definitions.Def_BlackbodyRadiation_planck

namespace BlackbodyRadiation
theorem planckShape_lt_planckShape_of_root
    (n : ℕ) (hn : 2 ≤ n) (x₀ : ℝ) (hx₀ : 0 < x₀)
    (hroot : x₀ = (n : ℝ) * (1 - Real.exp (-x₀))) :
    ∀ x : ℝ, 0 < x → x ≠ x₀ → planckShape n x < planckShape n x₀ := by sorry
end BlackbodyRadiation
