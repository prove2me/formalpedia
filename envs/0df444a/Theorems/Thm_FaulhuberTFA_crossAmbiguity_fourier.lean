-- Prove2me | Theorems.Thm_FaulhuberTFA_crossAmbiguity_fourier
-- name    : FaulhuberTFA.crossAmbiguity_fourier
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:52:49.556799+00:00
-- url     : https://prove2.me/theorems/8bcc76d7-8b3d-4e3d-8221-552c599c75e9
-- title:
--   Symmetric fundamental identity: $A(f,g)(x,\omega) = A(\hat f, \hat g)(\omega, -x)$
-- statement:
--   Let $f,g\in L^2(\mathbb{R}^d)$ with Fourier transforms $\hat f,\hat g$. For all $x,\omega\in\mathbb{R}^d$,
--
--   $$A(f,g)(x,\omega)=A(\hat f,\hat g)(\omega,-x).$$
--
--   This is the symmetric form of the fundamental identity: for the ambiguity function the rotation of the time-frequency plane carries no phase.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Section 3.3, display on p. 30

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem crossAmbiguity_fourier {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (x ω : Rd d) :
    crossAmbiguity f g x ω = crossAmbiguity (fourierL2 f) (fourierL2 g) ω (-x) := by sorry

end FaulhuberTFA
