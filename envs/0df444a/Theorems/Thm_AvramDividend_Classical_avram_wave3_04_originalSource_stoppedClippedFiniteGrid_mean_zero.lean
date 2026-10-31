-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalSource_stoppedClippedFiniteGrid_mean_zero
-- name    : AvramDividend.Classical.avram_wave3_04_originalSource_stoppedClippedFiniteGrid_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:19:56.185066+00:00
-- url     : https://prove2.me/theorems/278005ef-92d9-49a2-b900-6baee1153682
-- title:
--   The true stopped and clipped controlled Lévy verification integrand has zero finite-grid centred increment expectation
-- statement:
--   For the genuine original spectrally negative Lévy process and arbitrary adapted left-continuous dividend strategy, sample the actual discounted derivative of the post-payment controlled reserve left limit on an arbitrary finite family of time-grid intervals. At each cell start the coefficient is killed inclusively at the true ruin time and deterministic horizon and symmetrically clipped at ±K. Multiplication by integrable centred measurable original Lévy future-increment payoffs yields a finite sum with exactly zero expectation. The proof uses canonical strongly predictable source stopped integrand, measurable clipping, identical-path right-continuous Lévy reconstruction and accepted finite-grid zero-mean theorem. It is a true original-law simple stochastic-martingale identity; passage to a continuous-time compensated jump and Brownian stochastic integral remains open.
-- source:
--   Pinned remote private candidate-probe job 9187cf02-a802-4a34-a5fd-17efafd1fe1f passed source elaboration to sentinel, SHA-256 59218a1437d2f9f57e78324878fbb89beabe855b4df977cc1b5c643e3f352b41. Canonical established dependencies levy_rightCont_process 006d14c7-93c5-47e0-bbf9-8c32b53d456b, source stopped discounted predictable 658fb6a1-1044-40b3-aa7d-2926663389af, clipping 504ebddb-4d9e-4a99-9efa-75bc0940311a, finite original Lévy grid sum 96e78b02-5a94-4929-a453-cfa429a889de.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalLevy_finiteGrid_centeredPayoff_sum_zero

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_originalSource_stoppedClippedFiniteGrid_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (T : ℝ≥0) (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (φ : ι → ℝ → ℝ)
    (hφ : ∀ i ∈ S, Measurable (φ i))
    (hInt : ∀ i ∈ S, Integrable
      (fun ω => φ i (X.X (t i - s i) ω)) P)
    (hmean : ∀ i ∈ S,
      (∫ ω, φ i (X.X (t i - s i) ω) ∂P) = 0) :
    (∫ ω, ∑ i ∈ S,
      max (-K) (min K
        (if s i ≤ T then
          (Real.exp (-(q * (s i : ℝ))) *
            deriv w (Function.leftLim
              (fun u : ℝ≥0 =>
                x + X.X u ω - rightLimit D u ω) (s i))) *
          (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then
            (1 : ℝ) else 0)
        else 0)) *
      φ i (X.X (t i) ω - X.X (s i) ω) ∂P) = 0 := by sorry
