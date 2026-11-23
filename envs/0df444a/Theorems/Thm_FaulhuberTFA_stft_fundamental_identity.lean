-- Prove2me | Theorems.Thm_FaulhuberTFA_stft_fundamental_identity
-- name    : FaulhuberTFA.stft_fundamental_identity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:01:32.918199+00:00
-- url     : https://prove2.me/theorems/4348764b-9482-40f8-bd52-d3c1bc7bd549
-- title:
--   Proposition 2.5: fundamental identity of time-frequency analysis
-- statement:
--   Let $f,g\in L^2(\mathbb{R}^d)$ and let $\hat f,\hat g$ be their Fourier transforms. For all $x,\omega\in\mathbb{R}^d$,
--
--   $$V_gf(x,\omega)=e^{-2\pi i x\cdot\omega}\,V_{\hat g}\hat f(\omega,-x).$$
--
--   Up to a phase, the Fourier transform rotates the time-frequency plane: localising $f$ with the window $g$ is the same as localising $\hat f$ with the window $\hat g$.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Chapter 2, Proposition 2.5, eq. (2.2), p. 19

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem stft_fundamental_identity {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (x ω : Rd d) :
    stft g f x ω = ePhase (-⟪x, ω⟫_ℝ) * stft (fourierL2 g) (fourierL2 f) ω (-x) := by sorry

end FaulhuberTFA
