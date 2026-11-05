-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_weighted_diagonal_of_factorial_independent_future
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_weighted_diagonal_of_factorial_independent_future
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:32:21.187029+00:00
-- url     : https://prove2.me/theorems/32641b49-84a8-4b0b-8e8e-750c914241c1
-- title:
--   Physical finite-band predictable weighted L2 diagonal from factorial moments and future independence
-- statement:
--   For original intrinsic negative-band N_X on P and raw filtration, the weighted diagonal E[(H(N_X-r))²]=r E[H²] follows from physical first and second factorial count moments, source future sigma-algebra independence from F_s and explicit integrability. It removes the abstract conditional second-moment hypothesis. Does not claim the still Open original factorial-moment identity.
-- source:
--   Proved P4-B conditional original factorial variance 1b4ba10c and Proved P4-G original weighted diagonal 9b483610, strict -1<z<-epsilon small band.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_conditional_finite_band_variance_of_independent_future
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_weighted_diagonal_of_factorial_independent_future
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : X.ν B < ⊤)
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (r : ℝ)
    (hRate : r = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)
    (hJ : Integrable (fun ω => (N ω).toReal) P)
    (hFactorialIntegrable : Integrable (fun ω =>
      (N ω).toReal * ((N ω).toReal - 1)) P)
    (hFirst : (∫ ω, (N ω).toReal ∂P) = r)
    (hFactorial : (∫ ω,
      (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2)
    (mFuture : MeasurableSpace Ω) (hFuture : mFuture ≤ mΩ)
    (hSqMeas : StronglyMeasurable[mFuture]
      (fun ω => ((N ω).toReal - r) ^ 2))
    (hFutureIndependent : Indep mFuture (𝓕 s) P)
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hSqInt : Integrable (fun ω => ((N ω).toReal - r) ^ 2) P)
    (hHSqInt : Integrable (fun ω => (H ω) ^ 2) P)
    (hWeightedSqInt : Integrable
      (fun ω => (H ω) ^ 2 * ((N ω).toReal - r) ^ 2) P) :
    (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) =
      r * ∫ ω, (H ω) ^ 2 ∂P := by sorry
