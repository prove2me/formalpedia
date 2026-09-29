-- Prove2me | Theorems.Thm_EthierKurtz_state_dependent_diffusion_approximation
-- name    : EthierKurtz.state_dependent_diffusion_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:58:52.893091+00:00
-- url     : https://prove2.me/theorems/913c2e41-701d-4089-8434-2c0cb672dcb6
-- title:
--   Theorem 4.1 — state-dependent diffusion approximation from localized characteristics
-- statement:
--   Let a be a continuous symmetric positive-semidefinite covariance field and b a continuous drift, and assume the associated continuous-path martingale problem is well posed for every initial law. If càdlàg processes have local-martingale characteristics whose stopped jumps vanish, whose drift and covariance characteristics converge locally to the integrals of b and a along the state path, and whose initial laws converge weakly, then their complete path laws converge to the continuous diffusion law.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 7, Section 4, Theorem 4.1, printed p. 354 (PDF p. 363), equations (4.1)–(4.7); path-convergence conventions from Chapter 3, Theorem 1.8 and Proposition 5.3, printed pp. 102, 119.

import Definitions.Def_EthierKurtz_HasCadlagPaths
import Definitions.Def_EthierKurtz_IsSourceLocalMartingale
import Definitions.Def_EthierKurtz_diffusionExit
import Definitions.Def_EthierKurtz_expectedStoppedMaxJump
import Definitions.Def_EthierKurtz_diffusionDiscrepancy
import Definitions.Def_EthierKurtz_diffusionMatrixOperator
import Definitions.Def_EthierKurtz_IsContinuousDiffusionLaw

set_option autoImplicit true

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- All of (4.1)--(4.7), with full continuous-limit path convergence. -/
theorem state_dependent_diffusion_approximation
    {Ω : ℕ → Type*} [mΩ : ∀ n, MeasurableSpace (Ω n)] {d : ℕ}
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ha : Continuous a) (hb : Continuous b) (hapos : ∀ x, (a x).PosSemidef)
    (hwellposed : ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ∃! Q : ProbabilityMeasure {x : ℝ≥0 → EuclideanSpace ℝ (Fin d) // Continuous x},
        IsContinuousDiffusionLaw a b ν
          (Q : Measure {x : ℝ≥0 → EuclideanSpace ℝ (Fin d) // Continuous x})
          (fun t (x : {x : ℝ≥0 → EuclideanSpace ℝ (Fin d) // Continuous x}) => x.val t))
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X B : ∀ n, ℝ≥0 → Ω n → EuclideanSpace ℝ (Fin d))
    (A : ∀ n, ℝ≥0 → Ω n → Matrix (Fin d) (Fin d) ℝ)
    (hXmeas : ∀ n t, Measurable (X n t)) (hBmeas : ∀ n t, Measurable (B n t))
    (hAmeas : ∀ n t i j, Measurable (fun w => A n t w i j))
    (hXpath : ∀ n, HasCadlagPaths (X n)) (hBpath : ∀ n, HasCadlagPaths (B n))
    (hApath : ∀ n i j, HasCadlagPaths (fun t w => A n t w i j))
    (hAsym : ∀ n t w i j, A n t w i j = A n t w j i)
    (hAinc : ∀ n w s t, s < t → (A n t w - A n s w).PosSemidef)
    (ℱ : ∀ n, Filtration ℝ≥0 (mΩ n))
    (hℱ : ∀ n t, ℱ n t = ⨆ s : {s : ℝ≥0 // s ≤ t},
      (MeasurableSpace.comap (X n s.val) inferInstance ⊔
        MeasurableSpace.comap (B n s.val) inferInstance ⊔
        ⨆ i : Fin d, ⨆ j : Fin d,
          MeasurableSpace.comap (fun w => A n s.val w i j) inferInstance))
    (hM : ∀ n i, IsSourceLocalMartingale (P n) (ℱ n)
      (fun t w => X n t w i - B n t w i))
    (hMM : ∀ n i j, IsSourceLocalMartingale (P n) (ℱ n)
      (fun t w => (X n t w i - B n t w i) * (X n t w j - B n t w j) - A n t w i j))
    (hXjump : ∀ r : ℝ, 0 < r → ∀ T : ℝ≥0, 0 < T →
      Tendsto (fun n => expectedStoppedMaxJump (P n) (X n) 2 T (diffusionExit (X n) r))
        atTop (𝓝 0))
    (hBjump : ∀ r : ℝ, 0 < r → ∀ T : ℝ≥0, 0 < T →
      Tendsto (fun n => expectedStoppedMaxJump (P n) (B n) 2 T (diffusionExit (X n) r))
        atTop (𝓝 0))
    (hAjump : ∀ r : ℝ, 0 < r → ∀ T : ℝ≥0, 0 < T → ∀ i j,
      Tendsto (fun n => expectedStoppedMaxJump (P n) (fun t w => A n t w i j) 1 T
        (diffusionExit (X n) r)) atTop (𝓝 0))
    (hBconv : ∀ r : ℝ, 0 < r → ∀ T : ℝ≥0, 0 < T → ∀ i, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P n {w | ENNReal.ofReal ε ≤ diffusionDiscrepancy (X n)
        (fun t w => B n t w i) (fun x => b x i) T (diffusionExit (X n) r) w}) atTop (𝓝 0))
    (hAconv : ∀ r : ℝ, 0 < r → ∀ T : ℝ≥0, 0 < T → ∀ i j, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P n {w | ENNReal.ofReal ε ≤ diffusionDiscrepancy (X n)
        (fun t w => A n t w i j) (fun x => a x i j) T (diffusionExit (X n) r) w}) atTop (𝓝 0))
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)))
    (hinitial : ∀ f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ,
      Tendsto (fun n => ∫ w, f (X n 0 w) ∂P n) atTop (𝓝 (∫ x, f x ∂ν))) :
    ∃ Q : Measure
      ({x : ℝ≥0 → EuclideanSpace ℝ (Fin d) // Continuous x} ×
        (ℕ → {x : ℝ≥0 → EuclideanSpace ℝ (Fin d) //
          (∀ t, ContinuousWithinAt x (Set.Ici t) t) ∧
          ∀ t : ℝ≥0, 0 < t → ∃ v, Tendsto x (𝓝[<] t) (𝓝 v)})),
      IsProbabilityMeasure Q ∧
      (∀ n, Measure.map (fun z => (z.2 n).val) Q =
        Measure.map (fun w t => X n t w) (P n)) ∧
      IsContinuousDiffusionLaw a b ν Q (fun t z => z.1.val t) ∧
      (∀ᵐ z ∂Q, ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T → ‖(z.2 n).val t - z.1.val t‖ < ε) := by sorry
