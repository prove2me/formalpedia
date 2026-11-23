-- Prove2me | Theorems.Thm_FaulhuberTFA_stft_orthogonality_relations
-- name    : FaulhuberTFA.stft_orthogonality_relations
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:40:52.349537+00:00
-- url     : https://prove2.me/theorems/1fadc07b-b8ce-4458-afd6-ac65f0a40217
-- title:
--   Theorem 2.7: orthogonality relations (Moyal's identity) for the STFT
-- statement:
--   Let $f_1,f_2,g_1,g_2\in L^2(\mathbb{R}^d)$. Then $V_{g_1}f_1$ and $V_{g_2}f_2$ lie in $L^2(\mathbb{R}^{2d})$, and
--
--   $$\langle V_{g_1}f_1,V_{g_2}f_2\rangle_{L^2(\mathbb{R}^{2d})}=\iint_{\mathbb{R}^{2d}}V_{g_1}f_1(x,\omega)\,\overline{V_{g_2}f_2(x,\omega)}\,d(x,\omega)=\langle f_1,f_2\rangle\,\overline{\langle g_1,g_2\rangle},$$
--
--   with $\langle f,g\rangle=\int f\bar g$.
--
--   These are the orthogonality relations (Moyal's identity). They give the Plancherel-type isometry of the STFT, the inversion formula, and, for the ambiguity function, the radar "volume" law: the total squared ambiguity of a waveform is fixed by its energy.
-- source:
--   Faulhuber, Time-Frequency Analysis (Lecture Notes), arXiv:2204.01596 (2022), Chapter 2, Theorem 2.7, eq. (2.4), p. 20

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

theorem stft_orthogonality_relations {d : ℕ} {f₁ f₂ g₁ g₂ : Rd d → ℂ}
    (hf₁ : MemLp f₁ 2 volume) (hf₂ : MemLp f₂ 2 volume) (hg₁ : MemLp g₁ 2 volume) (hg₂ : MemLp g₂ 2 volume) :
    MemLp (fun p : Rd d × Rd d => stft g₁ f₁ p.1 p.2) 2 volume ∧
    MemLp (fun p : Rd d × Rd d => stft g₂ f₂ p.1 p.2) 2 volume ∧
    ∫ p : Rd d × Rd d, stft g₁ f₁ p.1 p.2 * starRingEnd ℂ (stft g₂ f₂ p.1 p.2) =
      l2inner f₁ f₂ * starRingEnd ℂ (l2inner g₁ g₂) := by sorry

end FaulhuberTFA
