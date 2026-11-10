-- Prove2me | Theorems.Thm_FiniteEnergyPlane_ae_eq_zero_of_fourier_eq_zero
-- name    : FiniteEnergyPlane.ae_eq_zero_of_fourier_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-09T22:23:43.151787+00:00
-- url     : https://prove2.me/theorems/3955b1dc-de37-4a51-b6a0-5fb50fa28513
-- title:
--   An integrable function on [0,1) with vanishing Fourier coefficients is zero
-- statement:
--   Let $H : \mathbb{R} \to \mathbb{C}$ be integrable on $[0,1)$ and suppose
--   $$\int_0^1 e^{2\pi i k t} H(t)\, dt = 0 \quad \text{for every } k \in \mathbb{Z}.$$
--   Then $H = 0$ almost everywhere on $[0,1)$.
--
--   **Role.** Uniqueness of Fourier coefficients for $L^1$ functions on the circle $\mathbb{R}/\mathbb{Z}$, stated for functions on the interval $[0,1)$ (the form in which loops in the $t$-variable of the cylinder $\mathbb{R}\times S^1$ appear).
-- source:
--   Standard Fourier uniqueness; Lemma in the setting of U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076

import Mathlib

namespace FiniteEnergyPlane

open MeasureTheory Filter Topology Set
open scoped ContDiff Real

/-- An integrable `H : ℝ → ℂ` on `[0, 1)` all of whose Fourier coefficients
`∫₀¹ e^{2πikt} H(t) dt`, `k ∈ ℤ`, vanish is zero almost everywhere on `[0, 1)`. -/
theorem ae_eq_zero_of_fourier_eq_zero (H : ℝ → ℂ) (hH : IntegrableOn H (Ico 0 1))
    (h : ∀ k : ℤ, ∫ t in Ico (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * k * t) * H t = 0) :
    ∀ᵐ t ∂(volume.restrict (Ico (0 : ℝ) 1)), H t = 0 := by
  sorry

end FiniteEnergyPlane
