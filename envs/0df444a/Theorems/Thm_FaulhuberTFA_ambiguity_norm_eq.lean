-- Prove2me | Theorems.Thm_FaulhuberTFA_ambiguity_norm_eq
-- name    : FaulhuberTFA.ambiguity_norm_eq
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:47:29.569846+00:00
-- url     : https://prove2.me/theorems/fdf45286-50a2-4773-b337-a4021ab6841d
-- title:
--   $\|Af\|_{L^2(\mathbb{R}^{2d})} = \|f\|_2^2$
-- statement:
--   Let $f\in L^2(\mathbb{R}^d)$. Then the ambiguity function satisfies
--
--   $$\|Af\|_{L^2(\mathbb{R}^{2d})}=\|f\|_{L^2(\mathbb{R}^d)}^2 .$$
--
--   This is the radar ambiguity "volume" law: the integral of $|Af|^2$ over the delay-Doppler plane equals the square of the signal's energy, whatever the waveform.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Section 3.3, display right after Definition 3.2, p. 26

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem ambiguity_norm_eq {d : ℕ} {f : Rd d → ℂ} (hf : MemLp f 2 volume) :
    eLpNorm (fun p : Rd d × Rd d => ambiguity f p.1 p.2) 2 volume = eLpNorm f 2 volume ^ 2 := by sorry

end FaulhuberTFA
