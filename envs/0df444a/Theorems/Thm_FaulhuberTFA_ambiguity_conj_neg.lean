-- Prove2me | Theorems.Thm_FaulhuberTFA_ambiguity_conj_neg
-- name    : FaulhuberTFA.ambiguity_conj_neg
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:47:00.644858+00:00
-- url     : https://prove2.me/theorems/bd5b34b7-0b9d-4895-b7fd-bf52d3f24770
-- title:
--   Symmetry of the ambiguity function: $\overline{Af(-x,-\omega)} = Af(x,\omega)$
-- statement:
--   Let $f\in L^2(\mathbb{R}^d)$ and $Af=A(f,f)$. For all $x,\omega\in\mathbb{R}^d$,
--
--   $$\overline{Af(-x,-\omega)}=Af(x,\omega).$$
--
--   In particular $Af(0,0)$ is real.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Section 3.3, display right after Definition 3.2, p. 26

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem ambiguity_conj_neg {d : ℕ} {f : Rd d → ℂ} (hf : MemLp f 2 volume) (x ω : Rd d) :
    starRingEnd ℂ (ambiguity f (-x) (-ω)) = ambiguity f x ω := by sorry

end FaulhuberTFA
