-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_lemma_3_7
-- name    : BLTCounting.AccuracySpace.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:22.800596+00:00
-- url     : https://prove2.me/theorems/09ea9186-13b0-4fe6-a601-b8aa35b1a209
-- title:
--   Positivity and strict monotonicity of the Fourier transform
-- statement:
--   Let $\widehat c_0$ be the Fourier transform of $c_0$. Then:
--
--   1. $\widehat c_0(x)$ is a non-negative, even function;
--   2. $\widehat c_0$ is strictly decreasing on $[0,\infty)$.
--
--   These properties make the threshold of Proposition 4.7 unique and let a pointwise symbol bound be read on a whole interval.
--
--   **Formalization Note.** $\widehat c_0$ is complex-valued by definition, so clause 1 includes that its imaginary part vanishes, and order statements are on its real part.
--
--   Differences from the source:
--   - encoding: the real-valued function $\widehat c_0$ → a complex integral with imaginary part stated to vanish, order on its real part; reason: Lean convention for the integral $\int c_0e^{-i\omega x}dx$; same function
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Lemma 3.7, printed p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel

namespace BLTCounting.AccuracySpace

/-- Lemma 3.7, PDF p. 18: (1) `ĉ₀` is real, non-negative and even; (2) `ĉ₀` is strictly decreasing on
`[0, ∞)`. Since `ĉ₀` is defined as a complex integral, realness is stated explicitly. -/
theorem lemma_3_7 :
    (∀ x : ℝ, (c0Hat x).im = 0 ∧ 0 ≤ (c0Hat x).re ∧ c0Hat (-x) = c0Hat x) ∧
      StrictAntiOn (fun x : ℝ => (c0Hat x).re) (Set.Ici 0) := by sorry

end BLTCounting.AccuracySpace
