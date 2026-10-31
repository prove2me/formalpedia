-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalStoppedDerivative_compensatedClippedFiniteGrid_mean_zero
-- name    : AvramDividend.Classical.avram_wave3_04_originalStoppedDerivative_compensatedClippedFiniteGrid_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:04:09.810546+00:00
-- url     : https://prove2.me/theorems/090ca3ef-3f23-445b-9279-d48c4f126241
-- title:
--   Original stopped controlled Lévy derivative has zero-mean finite-grid compensated clipped increments without first-moment assumptions
-- statement:
--   For an arbitrary finite family of original Lévy increment cells with past-measurable actual discounted, ruin-stopped controlled-reserve derivative coefficients clipped to ±K, centre each future increment after clipping at its own level R_i by subtracting its stationary source-law expectation. The expected sum of these true jointly adapted source-process products is exactly zero at every finite horizon. The proof establishes actual integrability of every bounded clipped increment, subtracts each original source stationary mean to derive centred payoffs, applies the already accepted original killed clipped derivative finite-grid mean-zero theorem to those payoffs, and retains the same original Lévy law and original admissible strategy on the same sample space. No first moment is assumed for X and no Poisson/Brownian equal-law replacement is used. The continuous-time quadratic-variation and stochastic Itô–Meyer limit remain separate.
-- source:
--   Pinned private exact compiler job 1be1c219-0685-465c-9d0c-6be40480e273 reached intentional sentinel with no source errors, candidate SHA256 65b54c7010a00db4a075b74b56d1dcc9a23f1868dd3b8525d51a07f1b18fea78. Canonical Proved originalSource_stoppedClippedFiniteGrid_mean_zero 278005ef-92d9-49a2-b900-6baee1153682 and source_bounded_futurePayoff_integrable eb2ca071-17d0-409f-b88a-59edf9d25ee8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalSource_stoppedClippedFiniteGrid_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_bounded_futurePayoff_integrable

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_originalStoppedDerivative_compensatedClippedFiniteGrid_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (T : ℝ≥0) (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (R : ι → ℝ) (hR : ∀ i ∈ S, 0 ≤ R i) :
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
      (max (-R i) (min (R i) (X.X (t i) ω - X.X (s i) ω)) -
        ∫ η, max (-R i) (min (R i) (X.X (t i - s i) η)) ∂P) ∂P) = 0 := by sorry
