-- Prove2me | Theorems.Thm_FaulhuberTFA_stft_gaussian
-- name    : FaulhuberTFA.stft_gaussian
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T11:00:09.099923+00:00
-- url     : https://prove2.me/theorems/25ca8f60-6085-4adf-af07-f364dd55faf6
-- title:
--   Example 2.3: the STFT of the standard Gaussian
-- statement:
--   Let $g_0(t)=2^{d/4}e^{-\pi|t|^2}$ be the standard Gaussian on $\mathbb{R}^d$. For all $x,\omega\in\mathbb{R}^d$,
--
--   $$V_{g_0}g_0(x,\omega)=e^{-\pi i x\cdot\omega}\,e^{-\frac{\pi}{2}(|x|^2+|\omega|^2)} .$$
--
--   The STFT of a Gaussian, taken with itself as window, is again a Gaussian in the time-frequency plane, with an explicit phase.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Chapter 2, Example 2.3, p. 17

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem stft_gaussian {d : ℕ} (x ω : Rd d) :
    stft (gauss0 d) (gauss0 d) x ω =
      Complex.exp (-(Real.pi * Complex.I * (⟪x, ω⟫_ℝ : ℂ))) *
        (Real.exp (-(Real.pi / 2) * (‖x‖ ^ 2 + ‖ω‖ ^ 2)) : ℂ) := by sorry

end FaulhuberTFA
