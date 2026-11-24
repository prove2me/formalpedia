-- Prove2me | Theorems.Thm_FaulhuberTFA_crossAmbiguity_eq_stft
-- name    : FaulhuberTFA.crossAmbiguity_eq_stft
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T11:46:36.688805+00:00
-- url     : https://prove2.me/theorems/a062ade3-1b82-4544-b3ce-57f7cc89aaae
-- title:
--   Definition 3.2: $A(f,g)(x,\omega) = e^{\pi i x\cdot\omega} V_g f(x,\omega)$
-- statement:
--   Let $f,g\in L^2(\mathbb{R}^d)$. For all $x,\omega\in\mathbb{R}^d$,
--
--   $$A(f,g)(x,\omega)=\int_{\mathbb{R}^d}f\big(t+\tfrac x2\big)\overline{g\big(t-\tfrac x2\big)}e^{-2\pi i\omega\cdot t}\,dt=e^{\pi i x\cdot\omega}\,V_gf(x,\omega).$$
--
--   The cross-ambiguity function is the STFT up to a phase, so every STFT property transfers to it.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Section 3.3, Definition 3.2, p. 25

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem crossAmbiguity_eq_stft {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (x ω : Rd d) :
    crossAmbiguity f g x ω = Complex.exp (Real.pi * Complex.I * (⟪x, ω⟫_ℝ : ℂ)) * stft g f x ω := by sorry

end FaulhuberTFA
