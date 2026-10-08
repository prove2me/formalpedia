-- Prove2me | Theorems.Thm_BesbesZeevi_Parametric_a17
-- name    : BesbesZeevi.Parametric.a17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:18:26.359742+00:00
-- url     : https://prove2.me/theorems/91d0e297-fe88-4a92-b6ea-21ea53827f9e
-- title:
--   Equation (A-17) — pricing-phase revenue lower bound
-- statement:
--   Let $Y_n^{(L)}$ be the learning-phase count and $Y_n^{(P)}$ the subsequent pricing-phase count under Algorithm 2. Its expected total revenue is at least the expected capped pricing-phase revenue:
--
--   $$J_n^\pi\ge\mathbb E\!\left[\widehat p\min\{Y_n^{(P)},(\lfloor nx\rfloor-Y_n^{(L)})^+\}\right].$$
--
--   The bound isolates the revenue available after learning. **Formalization Note** Whole-unit stock is $\lfloor nx\rfloor$, matching $nx$ when it is integral; the paper writes $nx$.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 32 (PDF p. 34), Step 1, Eq. (A-17)

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Algorithm

namespace BesbesZeevi.Parametric

open MeasureTheory

/-- Equation (A-17), p. 32, with the whole-unit inventory cap. -/
theorem a17 {k : ℕ} (D : Market) (F : Family k D)
    (S : OptimizerSelection D F) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (N : PoissonProcess Ω P) (n : ℕ) (hn : 1 ≤ n)
      (τ : ℝ) (hτ : 0 < τ) (hτT : τ ≤ D.T)
      (θstar : Fin k → ℝ), θstar ∈ F.Θ →
      (∫⁻ ω, ENNReal.ofReal
        (priceHat F S N n θstar τ ω *
          (((min
            (N.count (finalClock F S N n θstar τ ω) ω -
              N.count (learningClock F n θstar τ
                ⟨k, Nat.lt_succ_self k⟩) ω)
            (cap D n - N.count (learningClock F n θstar τ
              ⟨k, Nat.lt_succ_self k⟩) ω) : ℕ) : ℝ))) ∂P).toReal ≤
        jPolicy F S N n θstar τ := by sorry

end BesbesZeevi.Parametric
