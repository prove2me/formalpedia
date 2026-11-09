-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_equation_19
-- name    : BLTCounting.AccuracySpace.equation_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:35.77135+00:00
-- url     : https://prove2.me/theorems/c0301284-53d4-42a9-92b8-56aec3ee34cb
-- title:
--   Gamma-function formula for the transform of $c_0$
-- statement:
--   For every real $\omega$, the Fourier transform of the kernel $c_0(t)=(2\pi)^{-1/2}\mathrm{sech}^{1/2}(t/2)$ is
--   $$\widehat c_0(\omega)=\frac1\pi\Bigl|\Gamma\Bigl(\frac14+i\omega\Bigr)\Bigr|^2.$$
--   All positivity, monotonicity and decay properties of $\widehat c_0$ used by the mission are read from this formula.
--
--   Differences from the source: none.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Equation (19), printed p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel

open Complex

namespace BLTCounting.AccuracySpace

/-- Equation (19), PDF p. 18: `ĉ₀(ω) = |Γ(1/4 + iω)|² / π` for every real `ω`. -/
theorem equation_19 (ω : ℝ) :
    c0Hat ω = ((‖Complex.Gamma (1 / 4 + I * ω)‖ ^ 2 / Real.pi : ℝ) : ℂ) := by sorry

end BLTCounting.AccuracySpace
