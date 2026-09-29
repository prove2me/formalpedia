-- Prove2me | Theorems.Thm_EthierKurtz_martingale_central_limit
-- name    : EthierKurtz.martingale_central_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T05:58:11.332437+00:00
-- url     : https://prove2.me/theorems/cb4b8380-8ee1-4f24-b787-c8e02d8fc760
-- title:
--   Theorem 1.4 — martingale functional central limit theorem
-- statement:
--   For càdlàg vector local martingales with zero initial value and symmetric increasing matrix characteristics, either of the source’s two vanishing-jump alternatives, together with pointwise convergence in probability of the characteristics to a continuous deterministic covariance C, implies functional convergence to the centered continuous Gaussian process with covariance C(min(s,t)).
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 7, Section 1, Theorem 1.4, printed pp. 339–340 (PDF pp. 348–349); covariance conditions from Theorem 1.1, printed p. 338.

import Definitions.Def_EthierKurtz_HasCadlagPaths
import Definitions.Def_EthierKurtz_IsSourceLocalMartingale
import Definitions.Def_EthierKurtz_expectedMaxJump
import Definitions.Def_EthierKurtz_HasCrossVariation
import Definitions.Def_EthierKurtz_ConvergesToContinuousGaussian

set_option autoImplicit true

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- The martingale functional central limit theorem. Different n may live on
different probability spaces. No stationarity, prelimit independence, strict
positive definiteness, or predictable compensator is assumed. -/
theorem martingale_central_limit
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {d : ℕ}
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ℱ : ∀ n, Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω n)))
    (M : ∀ n, ℝ≥0 → Ω n → EuclideanSpace ℝ (Fin d))
    (A : ∀ n, ℝ≥0 → Ω n → Matrix (Fin d) (Fin d) ℝ)
    (hMmeas : ∀ n t, Measurable (M n t))
    (hMpaths : ∀ n, HasCadlagPaths (M n))
    (hMzero : ∀ n ω, M n 0 ω = 0)
    (hMlocal : ∀ n i, IsSourceLocalMartingale (P n) (ℱ n) (fun t ω => M n t ω i))
    (hAmeas : ∀ n t i j, Measurable (fun ω => A n t ω i j))
    (hApaths : ∀ n i j, HasCadlagPaths (fun t ω => A n t ω i j))
    (hAsym : ∀ n t ω i j, A n t ω i j = A n t ω j i)
    (hAinc : ∀ n ω (s t : ℝ≥0), s < t → (A n t ω - A n s ω).PosSemidef)
    (hjump :
      ((∀ T : ℝ≥0, 0 < T →
          Tendsto (fun n => expectedMaxJump (P n) (M n) 1 T) atTop (𝓝 0)) ∧
        (∀ n i j, HasCrossVariation (P n)
          (fun t ω => M n t ω i) (fun t ω => M n t ω j)
          (fun t ω => A n t ω i j))) ∨
      ((∀ (T : ℝ≥0), 0 < T → ∀ i j,
          Tendsto (fun n => expectedMaxJump (P n) (fun t ω => A n t ω i j) 1 T)
            atTop (𝓝 0)) ∧
        (∀ T : ℝ≥0, 0 < T →
          Tendsto (fun n => expectedMaxJump (P n) (M n) 2 T) atTop (𝓝 0)) ∧
        (∀ n i j, IsSourceLocalMartingale (P n) (ℱ n)
          (fun t ω => M n t ω i * M n t ω j - A n t ω i j))))
    (C : ℝ≥0 → Matrix (Fin d) (Fin d) ℝ)
    (hCcont : Continuous C) (hCzero : C 0 = 0)
    (hCsym : ∀ t i j, C t i j = C t j i)
    (hCinc : ∀ s t : ℝ≥0, s < t → (C t - C s).PosSemidef)
    (hAconv : ∀ t i j, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P n {ω | ε ≤ |A n t ω i j - C t i j|}) atTop (𝓝 0)) :
    ConvergesToContinuousGaussian P M C := by sorry
