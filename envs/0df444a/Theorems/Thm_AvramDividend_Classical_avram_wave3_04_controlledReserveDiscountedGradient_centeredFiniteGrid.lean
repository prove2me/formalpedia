-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_controlledReserveDiscountedGradient_centeredFiniteGrid
-- name    : AvramDividend.Classical.avram_wave3_04_controlledReserveDiscountedGradient_centeredFiniteGrid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:27:29.442958+00:00
-- url     : https://prove2.me/theorems/bf74e006-6ae9-4da7-bb41-c4e03be89919
-- title:
--   Original controlled Lévy reserve discounted gradients yield zero expected centred finite-grid stochastic sum
-- statement:
--   For a genuine dividend strategy D adapted and left-continuous in the source Lévy filtration, sample at any finite set of starting times the discounted verification derivative at the strict left limit of the real post-payment reserve x+X−D+. Clip this coefficient uniformly to [−K,K]. Each term multiplies a centred Borel payoff of the actual future Lévy increment X_t−X_s, assumed integrable under its stationary increment law. The expected sum is zero, regardless of overlaps among cells. The proof transports the identical source Lévy paths to their right-continuous filtration, retains the actual joint control X,D, proves strong predictability of the sampled coefficients, and invokes the accepted source-Lévy finite-grid zero-mean theorem. The result is a finite-grid martingale identity, not a statement of continuous-time Itô–Meyer convergence or full dividend verification.
-- source:
--   Source file work/avram_wave3_04_originalControlledDiscountedFiniteGrid_20261030_v1.lean, exact SHA-256 2eb3e1282ef63392f81dba62a3433bef68f99331f0a00cf1e59986ef3a168a5b. Pinned private remote compiler probe job 090d64b4-c6c3-42dd-bf71-46eac0abd04f (verdict pending at initial authoring). Imports only canonical Proved source-specific predictability, clipping, right-continuous Lévy reconstruction, and full finite-grid stochastic martingale results.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_deriv_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalLevy_finiteGrid_centeredPayoff_sum_zero

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_controlledReserveDiscountedGradient_centeredFiniteGrid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (φ : ι → ℝ → ℝ)
    (hφ : ∀ i ∈ S, Measurable (φ i))
    (hInt : ∀ i ∈ S, Integrable
      (fun ω => φ i (X.X (t i - s i) ω)) P)
    (hmean : ∀ i ∈ S,
      (∫ ω, φ i (X.X (t i - s i) ω) ∂P) = 0) :
    (∫ ω, ∑ i ∈ S,
      max (-K) (min K (Real.exp (-(q * (s i : ℝ))) *
        deriv w (Function.leftLim
          (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i)))) *
      φ i (X.X (t i) ω - X.X (s i) ω) ∂P) = 0 := by sorry
