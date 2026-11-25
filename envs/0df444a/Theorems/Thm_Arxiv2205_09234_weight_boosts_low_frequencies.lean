-- Prove2me | Theorems.Thm_Arxiv2205_09234_weight_boosts_low_frequencies
-- name    : Arxiv2205_09234.weight_boosts_low_frequencies
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T15:58:43.674226+00:00
-- url     : https://prove2.me/theorems/060e1b43-1f94-41e6-b2b1-b48a63de2fd0
-- title:
--   Section 3 (Marmousi model): $\mathrm W_\alpha$ boosts the low frequencies exactly when $\alpha<0$
-- statement:
--   Let $N\ge1$, $\Delta t>0$, $\alpha\in\mathbb{R}$, and let $\mathrm W_\alpha=\operatorname{diag}(w)$ be the weight matrix on the DFT sample frequencies $\omega_k$. For two sample frequencies with $0<|\omega_k|<|\omega_l|$,
--
--   $$w_l<w_k\iff\alpha<0.$$
--
--   So $\mathrm W_\alpha$ gives a lower frequency strictly more weight than a higher one exactly when $\alpha<0$; this is the paper's statement that the scaling of $\mathrm W_\alpha$ boosts the low frequencies and that this is only correct for $\alpha<0$.
--
--   **Formalization Note** "Boosts the low frequencies" is read as: lower nonzero frequencies receive strictly larger weight. The other parts of the paper's explanation (minimising an "energy difference", and the misfit turning into an $\ell_2$ misfit near the solution) are not stated.
-- source:
--   Izzatullah and Alkhalifah, omega-FWI: Robust full-waveform inversion with Fourier-based metric, arXiv:2205.09234v1 (2022), claim c010 (part (b)); Section 3, subsection Marmousi model, explanation paragraph, weight W_alpha of eqs. (2) and (5), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv2205_09234_Basic

open MeasureTheory Matrix

namespace Arxiv2205_09234

theorem weight_boosts_low_frequencies (N : ℕ) (hN : 0 < N) (dt α : ℝ) (hdt : 0 < dt)
    (w : Fin N → ℝ) (hw : IsFreqWeight N dt α w) (k l : Fin N)
    (hk : 0 < |sampleFreq N dt k|) (hkl : |sampleFreq N dt k| < |sampleFreq N dt l|) :
    w l < w k ↔ α < 0 := by sorry

end Arxiv2205_09234
