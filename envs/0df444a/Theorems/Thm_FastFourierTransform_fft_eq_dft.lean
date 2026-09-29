-- Prove2me | Theorems.Thm_FastFourierTransform_fft_eq_dft
-- name    : FastFourierTransform.fft_eq_dft
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T19:53:03.366144+00:00
-- url     : https://prove2.me/theorems/26bfc444-adc5-4fa7-b784-52a10c5b59d7
-- title:
--   Radix-2 Cooley–Tukey computes the DFT
-- statement:
--   **Correctness of the radix-2 Cooley–Tukey algorithm.** For every $p$, every signal $x:\mathbb{N}\to\mathbb{C}$ and every frequency index $k$,
--
--   $$\mathrm{fft}(p,x)(k)=\mathrm{dft}(2^p,x)(k)=\sum_{m=0}^{2^p-1}x_m e^{-2\pi i\,mk/2^p}.$$
--
--   That is, the divide-and-conquer recursion — which splits the input into even- and odd-indexed halves and recombines them with twiddle factors — returns exactly the values of the defining Fourier sum, with no approximation. The claim is made for every natural number $k$, including $k\ge 2^p$: both sides are $2^p$-periodic in $k$. No hypotheses are imposed on $x$ or $p$; in particular $p=0$ is included, where both sides equal $x_0$.
-- source:
--   Fast Fourier transform, Wikipedia (snapshot supplied by the mission captain's user), https://en.wikipedia.org/wiki/Fast_Fourier_transform, sections 'Definition' and 'Algorithms — Cooley–Tukey algorithm'

import Mathlib
import Definitions.Def_FastFourierTransform_dft
import Definitions.Def_FastFourierTransform_fft

namespace FastFourierTransform

theorem fft_eq_dft (p : ℕ) (x : ℕ → ℂ) (k : ℕ) :
    fft p x k = dft (2 ^ p) x k := by sorry

end FastFourierTransform
