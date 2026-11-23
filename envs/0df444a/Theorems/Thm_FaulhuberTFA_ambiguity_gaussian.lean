-- Prove2me | Theorems.Thm_FaulhuberTFA_ambiguity_gaussian
-- name    : FaulhuberTFA.ambiguity_gaussian
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:50:56.717297+00:00
-- url     : https://prove2.me/theorems/90f1bf39-d7c9-45c4-b7fa-f4aeb950abd4
-- title:
--   Example 3.4(b): the ambiguity function of the standard Gaussian
-- statement:
--   Let $g_0(t)=2^{1/4}e^{-\pi t^2}$ be the standard Gaussian on $\mathbb{R}$. For all $x,\omega\in\mathbb{R}$,
--
--   $$Ag_0(x,\omega)=e^{-\frac{\pi}{2}(x^2+\omega^2)} .$$
--
--   The Gaussian has a real, rotation-invariant ambiguity function concentrated at the origin, the benchmark of good joint delay-Doppler resolution.
--
--   **Formalization Note** $\mathbb{R}$ is represented as $\mathbb{R}^1$.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Section 3.3, Example 3.4(b), p. 28

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem ambiguity_gaussian (x ω : Rd 1) :
    ambiguity (gauss0 1) x ω = (Real.exp (-(Real.pi / 2) * (‖x‖ ^ 2 + ‖ω‖ ^ 2)) : ℂ) := by sorry

end FaulhuberTFA
