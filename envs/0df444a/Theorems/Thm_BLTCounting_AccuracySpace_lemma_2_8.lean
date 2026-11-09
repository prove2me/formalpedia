-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_lemma_2_8
-- name    : BLTCounting.AccuracySpace.lemma_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:35.924503+00:00
-- url     : https://prove2.me/theorems/e35044f7-74de-4518-9f2b-b22ac3e9b098
-- title:
--   Fourier transform of a hyperbolic cosine power
-- statement:
--   For every real $a>0$ and $\xi\in\mathbb R$,
--   $$\int_{-\infty}^{\infty}(\cosh t)^{-a}e^{-i\xi t}\,dt=\frac{2^{a-1}}{\Gamma(a)}\,\Gamma\!\Bigl(\frac{a+i\xi}2\Bigr)\Gamma\!\Bigl(\frac{a-i\xi}2\Bigr).$$
--   This classical formula (Gradshteyn–Ryzhik) gives the explicit transform of the kernel $c_0$.
--
--   Differences from the source: none.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Lemma 2.8, printed p. 12 (PDF p. 13)

import Mathlib

open Complex

namespace BLTCounting.AccuracySpace

/-- Lemma 2.8 (Gradshteyn–Ryzhik), PDF p. 13: for every `a > 0` and `ξ ∈ ℝ`,
`∫_{-∞}^{∞} (cosh t)^{-a} e^{-iξt} dt = (2^{a-1} / Γ(a)) Γ((a + iξ)/2) Γ((a - iξ)/2)`. -/
theorem lemma_2_8 (a ξ : ℝ) (ha : 0 < a) :
    ∫ t : ℝ, ((Real.cosh t ^ (-a) : ℝ) : ℂ) * cexp (-(I * ξ * t)) =
      (((2 : ℝ) ^ (a - 1) / Real.Gamma a : ℝ) : ℂ) *
        Complex.Gamma (((a : ℂ) + I * ξ) / 2) * Complex.Gamma (((a : ℂ) - I * ξ) / 2) := by sorry

end BLTCounting.AccuracySpace
