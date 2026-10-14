-- Prove2me | Theorems.Thm_DbarRegularity_fourierTransformL2_ae_eq_fourier
-- name    : DbarRegularity.fourierTransformL2_ae_eq_fourier
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T14:37:50.092342+00:00
-- url     : https://prove2.me/theorems/b4091587-2cbb-4bc6-8640-5877824e9743
-- title:
--   On $L^1\cap L^2$ the $L^2$ Fourier transform agrees a.e. with the Fourier integral
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Lebesgue (Haar) measure, and let $g:E\to\mathbb C$ be integrable and square integrable. Then the Fourier–Plancherel transform of $g$, regarded as an element of $L^2(E)$, coincides almost everywhere with the Fourier integral
--   $$\hat g(\xi)=\int_E e^{-2\pi i\langle x,\xi\rangle}\,g(x)\,dx .$$
--
--   This identifies the abstract unitary Fourier transform on $L^2$ with the classical integral formula on $L^1\cap L^2$, so that identities known for the integral transform of integrable functions can be read in $L^2$.
--
--   **Formalization Note.** The $L^2$ transform is Mathlib's `Lp.fourierTransformₗᵢ E ℂ`, applied to `hg2.toLp g`; the integral transform is `𝓕 g`, Mathlib's Fourier integral with kernel $e^{-2\pi i\langle x,\xi\rangle}$. The conclusion is an almost-everywhere equality of functions $E\to\mathbb C$ with respect to `volume`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, p. 28

import Mathlib.Analysis.Fourier.LpSpace

namespace DbarRegularity

open MeasureTheory FourierTransform
open scoped ENNReal

/-- For `g ∈ L¹ ∩ L²` on a finite-dimensional real inner product space, the Fourier transform of
`g` as an element of `L²` agrees almost everywhere with the Fourier integral
`𝓕 g ξ = ∫ e^{-2πi⟪x, ξ⟫} g x dx`. -/
theorem fourierTransformL2_ae_eq_fourier {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (g : E → ℂ) (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume) :
    (Lp.fourierTransformₗᵢ E ℂ (hg2.toLp g) : E → ℂ) =ᵐ[volume] 𝓕 g := by sorry

end DbarRegularity
