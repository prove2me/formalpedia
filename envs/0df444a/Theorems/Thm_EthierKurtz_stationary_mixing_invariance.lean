-- Prove2me | Theorems.Thm_EthierKurtz_stationary_mixing_invariance
-- name    : EthierKurtz.stationary_mixing_invariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:00:11.237907+00:00
-- url     : https://prove2.me/theorems/3dd004d8-b940-4e7a-869b-bc26a86af940
-- title:
--   Theorem 3.1 — stationary-sequence Brownian invariance principle
-- statement:
--   Let a two-sided real sequence be strictly stationary, measurable, and centered. If it has a finite (2+δ)-moment for some δ>0 and the δ/(1+δ) powers of its Lp mixing coefficients are summable for p=(2+δ)/(1+δ), then its ordered covariance series converges, its resulting variance is nonnegative, and the scaled partial-sum processes converge in the full path-law sense to centered Brownian motion with that variance, including the zero-variance case.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 7, Section 3, Theorem 3.1 and equations (3.1)–(3.4), printed pp. 350–351 (PDF pp. 359–360); mixing definition in equation (2.3), printed p. 346 (PDF p. 355).

import Definitions.Def_EthierKurtz_ConvergesToContinuousGaussian
import Definitions.Def_EthierKurtz_stationaryLpMixing
import Definitions.Def_EthierKurtz_stationaryPartialSums

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- The stationary mixing invariance principle. Shift-invariance of the
whole sequence law expresses strict stationarity. The covariance series is
stated as an ordered partial-sum limit. The reused conclusion specifies full
path convergence to Brownian motion, including the zero-variance case. -/
theorem stationary_mixing_invariance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℤ → Ω → ℝ)
    (hYmeas : ∀ k, Measurable (Y k))
    (hstationary : ∀ l : ℤ,
      Measure.map (fun ω k => Y (k + l) ω) P =
        Measure.map (fun ω k => Y k ω) P)
    (hcentered : ∀ k, ∫ ω, Y k ω ∂P = 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hmoment : ∀ k, MemLp (Y k) (ENNReal.ofReal (2 + δ)) P)
    (hmixing :
      (∑' m : ℕ, (stationaryLpMixing P Y ((2 + δ) / (1 + δ)) m) ^
        (δ / (1 + δ))) < ∞) :
    ∃ c : ℝ,
      Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
        ∫ ω, Y 1 ω * Y ((k : ℤ) + 2) ω ∂P) atTop (𝓝 c) ∧
      0 ≤ (∫ ω, (Y 1 ω) ^ 2 ∂P) + 2 * c ∧
      ConvergesToContinuousGaussian (fun _ : ℕ => P) (stationaryPartialSums Y)
        (fun t _ _ => (t : ℝ) * ((∫ ω, (Y 1 ω) ^ 2 ∂P) + 2 * c)) := by sorry
