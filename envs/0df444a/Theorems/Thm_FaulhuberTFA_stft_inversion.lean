-- Prove2me | Theorems.Thm_FaulhuberTFA_stft_inversion
-- name    : FaulhuberTFA.stft_inversion
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T11:46:05.330178+00:00
-- url     : https://prove2.me/theorems/7394ec1d-7934-4654-a220-19457fb3fc7c
-- title:
--   Theorem 2.9: inversion formula for the STFT
-- statement:
--   Let $g,\tilde g\in L^2(\mathbb{R}^d)$ with $\langle\tilde g,g\rangle\neq0$, and let $f\in L^2(\mathbb{R}^d)$. Then
--
--   $$f=\frac{1}{\langle\tilde g,g\rangle}\iint_{\mathbb{R}^{2d}}V_gf(x,\omega)\,M_\omega T_x\tilde g\;d(x,\omega),$$
--
--   where the function-valued integral is understood in the weak sense the notes use (p. 22): for every $h\in L^2(\mathbb{R}^d)$,
--
--   $$\langle f,h\rangle=\frac{1}{\langle\tilde g,g\rangle}\iint_{\mathbb{R}^{2d}}V_gf(x,\omega)\,\langle M_\omega T_x\tilde g,h\rangle\,d(x,\omega).$$
--
--   A signal is recovered from its STFT as a superposition of time-frequency shifted copies of a synthesis window $\tilde g$, which may differ from the analysis window $g$.
--
--   **Formalization Note** The statement is the weak form displayed second, quantified over all $h\in L^2(\mathbb{R}^d)$; this is how the notes define the vector-valued integral.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Chapter 2, Theorem 2.9, eq. (2.6), p. 22, with the weak meaning of the vector-valued integral defined on p. 22

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem stft_inversion {d : ℕ} {f g g' : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hg' : MemLp g' 2 volume) (hgg' : l2inner g' g ≠ 0) (h : Rd d → ℂ) (hh : MemLp h 2 volume) :
    l2inner f h = (l2inner g' g)⁻¹ *
      ∫ p : Rd d × Rd d, stft g f p.1 p.2 * l2inner (modul p.2 (transl p.1 g')) h := by sorry

end FaulhuberTFA
