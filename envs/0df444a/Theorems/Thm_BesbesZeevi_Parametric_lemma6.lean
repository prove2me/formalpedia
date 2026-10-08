-- Prove2me | Theorems.Thm_BesbesZeevi_Parametric_lemma6
-- name    : BesbesZeevi.Parametric.lemma6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:19:07.578797+00:00
-- url     : https://prove2.me/theorems/a36a3cb9-ead6-4a69-8597-db4846d6c12d
-- title:
--   Lemma 6 — expected parameter-estimation error
-- statement:
--   Under Assumption 2, there is a finite positive constant $C_2$, independent of the true $\theta^*\in\Theta$, the market size, and the Poisson realization, such that for every $n\ge1$ and $0<\tau_n\le T$,
--
--   $$\mathbb E\|\widehat\theta-\theta^*\|_\infty\le\frac{C_2}{\sqrt{n\tau_n}}.$$
--
--   The estimate is the inverse $g$ applied to normalized test-price count increments. This controls the statistical error entering the final price. **Formalization Note** The expectation is a nonnegative integral; $g$ maps into compact $\Theta$.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 34 (PDF p. 36), Lemma 6, Eq. (A-24); proof p. 44 (PDF p. 46)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Algorithm

namespace BesbesZeevi.Parametric

open MeasureTheory

/-- Lemma 6, p. 34: the expected sup-norm error of the inverse estimate. -/
theorem lemma6 {k : ℕ} (D : Market) (F : Family k D) :
    ∃ C2 : ℝ, 0 < C2 ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (N : PoissonProcess Ω P) (n : ℕ) (hn : 1 ≤ n)
        (τ : ℝ) (hτ : 0 < τ) (hτT : τ ≤ D.T) (θstar : Fin k → ℝ),
        θstar ∈ F.Θ →
        (∫⁻ ω, ENNReal.ofReal (‖thetaHat F N n θstar τ ω - θstar‖) ∂P).toReal ≤
          C2 / Real.sqrt ((n : ℝ) * τ) := by sorry

end BesbesZeevi.Parametric
