-- Prove2me | Theorems.Thm_FastFourierTransform_idft_dft
-- name    : FastFourierTransform.idft_dft
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:29:29.788366+00:00
-- url     : https://prove2.me/theorems/209f5529-8375-4e18-ad8e-8192049bbadc
-- title:
--   Fourier inversion for the DFT
-- statement:
--   **Fourier inversion.** For $n\ge 1$, every signal $x$ and every sample index $m<n$,
--
--   $$\frac1n\sum_{k=0}^{n-1}\Big(\sum_{j=0}^{n-1}x_j e^{-2\pi i\,jk/n}\Big)e^{+2\pi i\,mk/n}=x_m.$$
--
--   Applying the inverse transform of length $n$ to the transform of length $n$ recovers the original samples exactly on the window $\{0,\dots,n-1\}$. Nothing is claimed for $m\ge n$, where $x_m$ never entered the transform. The proof rests on the orthogonality relation $\sum_{k<n}e^{2\pi i(m-j)k/n}=n$ when $m\equiv j \pmod n$ and $0$ otherwise.
-- source:
--   Fast Fourier transform, Wikipedia (snapshot supplied by the mission captain's user), https://en.wikipedia.org/wiki/Fast_Fourier_transform, section 'Definition' (inverse DFT: same transform with opposite sign and a 1/n factor)

import Mathlib
import Definitions.Def_FastFourierTransform_dft
import Definitions.Def_FastFourierTransform_idft

namespace FastFourierTransform

theorem idft_dft (n : ℕ) (hn : 0 < n) (x : ℕ → ℂ) (m : ℕ) (hm : m < n) :
    idft n (dft n x) m = x m := by sorry

end FastFourierTransform
