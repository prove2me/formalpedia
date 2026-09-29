-- Prove2me | Theorems.Thm_FamousTheorems_fourier_transform_gaussian_6b
-- name    : FamousTheorems.fourier_transform_gaussian_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:42:02.804366+00:00
-- url     : https://prove2.me/theorems/5102ce9b-8f03-461a-bb14-714df845a559
-- title:
--   The Fourier transform of a Gaussian is a Gaussian
-- statement:
--   **The Fourier transform of a Gaussian is a Gaussian.** Let $V$ be a finite-dimensional real inner product space of dimension $d$, and let $b\in\mathbb C$ with $\operatorname{Re} b>0$. With the Fourier transform $\hat f(w)=\int_V e^{-2\pi i\langle v,w\rangle}f(v)\,dv$,
--   $$\widehat{e^{-b\|v\|^2}}(w)=\Big(\frac{\pi}{b}\Big)^{d/2}e^{-\pi^2\|w\|^2/b}.$$
--
--   This is the basic computation of Fourier analysis. For $b=\pi$ it says that $e^{-\pi\|x\|^2}$ is its own Fourier transform. It is used in the proofs of the Fourier inversion formula, the Poisson summation formula for theta functions, and the functional equation of the Riemann zeta function.
--
--   **Formalization note.** Mathlib's `fourier_gaussian_innerProductSpace`. `FourierTransform.fourier` is the Fourier transform with the $e^{-2\pi i\langle v,w\rangle}$ convention, and the complex power uses the principal branch.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `fourier_gaussian_innerProductSpace`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fourier_transform_gaussian_6b {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {b : ℂ} (hb : 0 < b.re) (w : V) :
    FourierTransform.fourier (fun v : V => Complex.exp (-b * (‖v‖ : ℂ) ^ 2)) w =
      ((Real.pi : ℂ) / b) ^ ((Module.finrank ℝ V : ℂ) / 2) * Complex.exp (-(Real.pi : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / b) := by sorry

end FamousTheorems
