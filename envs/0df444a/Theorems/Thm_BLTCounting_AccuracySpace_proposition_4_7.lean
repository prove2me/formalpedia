-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_proposition_4_7
-- name    : BLTCounting.AccuracySpace.proposition_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:34.899148+00:00
-- url     : https://prove2.me/theorems/8a5cc9ae-7d8c-4341-a56c-78615b67997a
-- title:
--   Existence and asymptotics of the Fourier threshold
-- statement:
--   Write $\eta=e^{-A}$. There is an absolute constant $a_*>0$ such that for every $A\ge a_*$ there is a unique $\omega_*>0$ with $\widehat c_0(\omega_*)=8\eta$. Moreover, as $A\to\infty$,
--   $$\omega_*=\frac1\pi\Bigl(A-\frac12\log A+O(1)\Bigr).$$
--   The frequency $\omega_*$ controls the width of the band on which the Toeplitz symbol exceeds the threshold, and it supplies the factor $\log(1/\eta)$ in the goal.
--
--   **Formalization Note.** The $O(1)$ is an absolute constant valid for $A\ge A_0$; the statement is written for $\eta>0$ with $A=\log(1/\eta)$.
--
--   Differences from the source: none.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Proposition 4.7, printed p. 28 (PDF p. 29)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel

namespace BLTCounting.AccuracySpace

/-- Proposition 4.7, PDF p. 29: there is an absolute `a_* > 0` such that `A = log(1/η) ≥ a_*` implies a
unique `ω_* > 0` with `ĉ₀(ω_*) = 8η`; moreover `ω_* = (1/π)(A - (1/2) log A + O(1))` as `A → ∞`. -/
theorem proposition_4_7 :
    ∃ a : ℝ, 0 < a ∧
      (∀ η : ℝ, 0 < η → a ≤ Real.log (1 / η) →
        ∃! ω : ℝ, 0 < ω ∧ c0Hat ω = ((8 * η : ℝ) : ℂ)) ∧
      ∃ C A₀ : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → A₀ ≤ Real.log (1 / η) →
        ∀ ω : ℝ, 0 < ω → c0Hat ω = ((8 * η : ℝ) : ℂ) →
          |ω - (1 / Real.pi) * (Real.log (1 / η) - (1 / 2) * Real.log (Real.log (1 / η)))| ≤ C := by sorry

end BLTCounting.AccuracySpace
