-- Prove2me | Theorems.Thm_FastFourierTransform_dft_conj_symm
-- name    : FastFourierTransform.dft_conj_symm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:32:04.073519+00:00
-- url     : https://prove2.me/theorems/6c7c0a90-651d-45da-a0a3-38986ea7e5ce
-- title:
--   Conjugate symmetry of the spectrum of a real signal
-- statement:
--   **Conjugate symmetry for real inputs.** If every sample $x_m$ is real, then for every $k\le n$
--
--   $$X_{n-k}=\overline{X_k},\qquad X_j:=\mathrm{dft}(n,x)(j).$$
--
--   The spectrum of a real signal is determined by its first half, which is what real-input FFT algorithms exploit to save roughly a factor of two in time and memory. The hypothesis is that $x_m$ has zero imaginary part for every natural number $m$; the subtraction $n-k$ is taken with $k\le n$, so it is ordinary subtraction.
-- source:
--   Fast Fourier transform, Wikipedia (snapshot supplied by the mission captain's user), https://en.wikipedia.org/wiki/Fast_Fourier_transform, section 'FFT algorithms specialized for real or symmetric data' (the symmetry $X_{n-k}=X_k^*$)

import Mathlib
import Definitions.Def_FastFourierTransform_dft

namespace FastFourierTransform

theorem dft_conj_symm (n : ℕ) (x : ℕ → ℂ) (hx : ∀ m, (x m).im = 0) (k : ℕ) (hk : k ≤ n) :
    dft n x (n - k) = (starRingEnd ℂ) (dft n x k) := by sorry

end FastFourierTransform
