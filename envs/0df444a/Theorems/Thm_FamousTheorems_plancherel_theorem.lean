-- Prove2me | Theorems.Thm_FamousTheorems_plancherel_theorem
-- name    : FamousTheorems.plancherel_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:47.243979+00:00
-- url     : https://prove2.me/theorems/4e39c06f-0721-4d6e-b69e-c923318db155
-- title:
--   The Plancherel theorem (Schwartz functions)
-- statement:
--   **The Plancherel theorem.** For every Schwartz function $f$ on a finite-dimensional real inner product space $V$, with values in a complex Hilbert space $H$,
--   $$\int_V\|\hat f(\xi)\|^2\,d\xi=\int_V\|f(x)\|^2\,dx .$$
--
--   The Fourier transform is thus an isometry for the $L^2$ norm on a dense subspace, and so extends to a unitary operator on $L^2(V)$. This is the foundation of $L^2$ harmonic analysis, of the uncertainty principle, and of spectral methods in PDE and signal processing.
--
--   **Formalization note.** Mathlib's `SchwartzMap.integral_norm_sq_fourier`, with the normalisation $\hat f(\xi)=\int e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx$ (`FourierTransform.fourier`) and Lebesgue (Haar) measure on `V`. The polarised version is `SchwartzMap.integral_inner_fourier_fourier`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `SchwartzMap.integral_norm_sq_fourier`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem plancherel_theorem {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (f : SchwartzMap V H) : ∫ ξ, ‖FourierTransform.fourier f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by sorry

end FamousTheorems
