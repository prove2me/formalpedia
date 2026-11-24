-- Prove2me | Theorems.Thm_FaulhuberTFA_stft_norm_eq
-- name    : FaulhuberTFA.stft_norm_eq
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T11:43:32.964132+00:00
-- url     : https://prove2.me/theorems/5baf1fec-0fdb-4bc8-9cd8-a1d115c7acfd
-- title:
--   Corollary 2.8: $\|V_g f\|_2 = \|f\|_2 \|g\|_2$
-- statement:
--   Let $f,g\in L^2(\mathbb{R}^d)$. Then
--
--   $$\|V_gf\|_{L^2(\mathbb{R}^{2d})}=\|f\|_2\,\|g\|_2 .$$
--
--   In particular, if $\|g\|_2=1$ then $\|f\|_2=\|V_gf\|_2$, so the STFT with a unit-norm window is an isometry from $L^2(\mathbb{R}^d)$ into $L^2(\mathbb{R}^{2d})$.
--
--   **Formalization Note** Norms are Mathlib's $L^2$ seminorms with values in $[0,\infty]$; on $L^2$ functions they are the usual finite norms.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Chapter 2, Corollary 2.8, eq. (2.5), p. 20

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem stft_norm_eq {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    eLpNorm (fun p : Rd d × Rd d => stft g f p.1 p.2) 2 volume = eLpNorm f 2 volume * eLpNorm g 2 volume ∧
    (eLpNorm g 2 volume = 1 → eLpNorm f 2 volume = eLpNorm (fun p : Rd d × Rd d => stft g f p.1 p.2) 2 volume) := by sorry

end FaulhuberTFA
