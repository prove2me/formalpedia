-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_equation_20
-- name    : BLTCounting.AccuracySpace.equation_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:19.371535+00:00
-- url     : https://prove2.me/theorems/49ca0aba-1780-4a49-ac02-4b795fe87d23
-- title:
--   Large-frequency asymptotic of $\widehat c_0$
-- statement:
--   As $\omega\to\infty$,
--   $$\widehat c_0(\omega)=2\,\omega^{-1/2}e^{-\pi\omega}\bigl(1+O(\omega^{-1})\bigr).$$
--   The leading factor $2$ and the exponent $\pi$ are what fix the size of the threshold in Proposition 4.7.
--
--   **Formalization Note.** The $O$ term is stated with constants $C,W>0$: for $\omega\ge W$ the difference is at most $(C/\omega)\cdot2\omega^{-1/2}e^{-\pi\omega}$ in modulus.
--
--   Differences from the source: none.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Equation (20), printed p. 18 (PDF p. 19)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel

namespace BLTCounting.AccuracySpace

/-- Equation (20), PDF p. 19: `ĉ₀(ω) = 2 ω^{-1/2} e^{-πω} (1 + O(ω⁻¹))` as `ω → ∞`. -/
theorem equation_20 :
    ∃ C W : ℝ, 0 < C ∧ 0 < W ∧ ∀ ω : ℝ, W ≤ ω →
      ‖c0Hat ω - ((2 * ω ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * ω)) : ℝ) : ℂ)‖ ≤
        (C / ω) * (2 * ω ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * ω))) := by sorry

end BLTCounting.AccuracySpace
