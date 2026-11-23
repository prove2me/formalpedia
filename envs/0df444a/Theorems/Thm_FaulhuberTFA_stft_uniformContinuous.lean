-- Prove2me | Theorems.Thm_FaulhuberTFA_stft_uniformContinuous
-- name    : FaulhuberTFA.stft_uniformContinuous
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:00:37.957984+00:00
-- url     : https://prove2.me/theorems/099b9ea0-121b-46c4-bac0-c553afa7aa95
-- title:
--   Lemma 2.4: the STFT of $L^2$ functions is uniformly continuous
-- statement:
--   Let $f,g\in L^2(\mathbb{R}^d)$. Then the short-time Fourier transform
--
--   $$(x,\omega)\longmapsto V_gf(x,\omega)=\int_{\mathbb{R}^d}f(t)\overline{g(t-x)}e^{-2\pi i\omega\cdot t}\,dt$$
--
--   is uniformly continuous on $\mathbb{R}^{2d}$.
--
--   This is the basic regularity of the STFT: whatever the signal and window, the time-frequency picture has no jumps.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Chapter 2, Lemma 2.4, p. 18

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem stft_uniformContinuous {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    UniformContinuous (fun p : Rd d × Rd d => stft g f p.1 p.2) := by sorry

end FaulhuberTFA
