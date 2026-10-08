-- Prove2me | Theorems.Thm_BesbesZeevi_Parametric_parametric_regret_bound
-- name    : BesbesZeevi.Parametric.parametric_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:19:18.887997+00:00
-- url     : https://prove2.me/theorems/c2f30c67-f5c2-47df-9fa0-1307a802137f
-- title:
--   Proposition 3 — parametric regret bound
-- statement:
--   Let $\Theta\subseteq\mathbb R^k$ be a compact convex parameter set and let the whole demand family satisfy Assumptions 1 and 2 with common constants. Algorithm 2 tests the distinct prices of Assumption 2, estimates $\theta$ from Poisson demand, and then prices at the larger of the two continuous optimizers. If $\tau_n\asymp n^{-1/3}$, there is a finite positive constant $C$, uniform over $\theta\in\Theta$ and market size, such that
--
--   $$\sup_{\theta\in\Theta}R_n^\pi(x,T;\theta)\le C\frac{\sqrt{\log n}}{n^{1/3}},\qquad n\ge2.$$
--
--   The result quantifies the revenue loss from learning an unknown finite-dimensional demand parameter while stock is limited. **Formalization Note** The printed equation says $n\ge1$, but at $n=1$ its right side is zero; the finite-size case is absorbed into the constant and the theorem starts at $n=2$. Whole-unit stock is $\lfloor nx\rfloor$. Assumption 2(i)b is interpreted through a Lipschitz estimate map into $\Theta$ that recovers every true parameter; this permits the paper's use of Assumption 2(ii) at the estimate. The asymptotic tuning bounds hold after a fixed threshold.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 16 (PDF p. 18), Proposition 3, Eq. (17)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Algorithm

namespace BesbesZeevi.Parametric

open MeasureTheory

/-- Proposition 3, equation (17), p. 16, for Algorithm 2 in the scaled market. -/
theorem parametric_regret_bound {k : ℕ} (D : Market) (F : Family k D)
    (c c' : ℝ) (hc : 0 < c) (hcc' : c ≤ c') (n0 : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : OptimizerSelection D F) (τ : ℕ → ℝ),
      (∀ n : ℕ, 2 ≤ n → 0 < τ n ∧ τ n ≤ D.T) →
      (∀ n : ℕ, n0 ≤ n →
        c * (n : ℝ) ^ (-(1 : ℝ) / 3) ≤ τ n ∧
        τ n ≤ c' * (n : ℝ) ^ (-(1 : ℝ) / 3)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (N : PoissonProcess Ω P) (n : ℕ),
        2 ≤ n → ∀ θstar : Fin k → ℝ, θstar ∈ F.Θ →
        regret F S N n θstar (τ n) ≤
          C * Real.sqrt (Real.log (n : ℝ)) / (n : ℝ) ^ ((1 : ℝ) / 3) := by sorry

end BesbesZeevi.Parametric
