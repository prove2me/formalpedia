-- Prove2me | Theorems.Thm_BesbesZeevi_Parametric_a25
-- name    : BesbesZeevi.Parametric.a25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:19:02.215401+00:00
-- url     : https://prove2.me/theorems/b2c9a327-98ee-48ab-a7f5-f7922f20f9e5
-- title:
--   Equation (A-25) — general tuning regret bound
-- statement:
--   For Algorithm 2 under the tuning of Proposition 3, there is a positive constant $C_3$, uniform over parameters, measurable optimizer choices, and Poisson spaces, such that
--
--   $$R_n^\pi(x,T;\theta^*)\le\frac{C_3}{m^D}\left(\tau_n+\frac{\sqrt{\log n}}{\sqrt{n\tau_n}}\right),\qquad m^D=m\min\{T,x/M\}.$$
--
--   This is the last quantitative estimate before substituting the learning-time scale. **Formalization Note** The asymptotic comparison $\tau_n\asymp n^{-1/3}$ is encoded by fixed positive lower and upper constants beyond a fixed threshold. The displayed bound is stated for $n\ge2$, because $\log1=0$ does not represent the finite-size error.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 34 (PDF p. 36), Step 4, Eq. (A-25)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Algorithm

namespace BesbesZeevi.Parametric

open MeasureTheory

/-- Equation (A-25), p. 34, under the Proposition 3 tuning. -/
theorem a25 {k : ℕ} (D : Market) (F : Family k D)
    (c c' : ℝ) (hc : 0 < c) (hcc' : c ≤ c') (n0 : ℕ) :
    ∃ C3 : ℝ, 0 < C3 ∧
      ∀ (S : OptimizerSelection D F) (τ : ℕ → ℝ),
      (∀ n : ℕ, 2 ≤ n → 0 < τ n ∧ τ n ≤ D.T) →
      (∀ n : ℕ, n0 ≤ n →
        c * (n : ℝ) ^ (-(1 : ℝ) / 3) ≤ τ n ∧
        τ n ≤ c' * (n : ℝ) ^ (-(1 : ℝ) / 3)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (N : PoissonProcess Ω P) (n : ℕ),
        2 ≤ n → ∀ θstar : Fin k → ℝ, θstar ∈ F.Θ →
        regret F S N n θstar (τ n) ≤
          C3 / (D.m * min D.T (D.x / D.M)) *
            (τ n + Real.sqrt (Real.log (n : ℝ)) /
              Real.sqrt ((n : ℝ) * τ n)) := by sorry

end BesbesZeevi.Parametric
