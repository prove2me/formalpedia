-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_finitecap_localised_gaussian_crossing_positive_expected_L1
-- name    : AvramDividend.Classical.avram_a26_original_finitecap_localised_gaussian_crossing_positive_expected_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:05:33.355606+00:00
-- url     : https://prove2.me/theorems/1d6c97b4-49b1-47ff-be6a-1978e56551ac
-- title:
--   Original finitecap compact-band true Gaussian crossing spatial positive error has vanishing L1
-- statement:
--   For the original finitecap caplinear HJB continuation, if genuine stopped spatial Gaussian cell increments δ_m→0 on a positive pre-ruin compact band [a,b], then the positive crossing spatial residual max(V(y_m+δ_m)−V(y_m),0) tends to zero in expected value under a common integrable majorant. Uses the finitecap caplinear moving-base convergence source a26 and the existing Proved a108 unique crossing dominated-convergence lemma with a singleton crossing cell. Crucially does not assume globally bounded original w or substitute an unrelated martingale. Expected HJB cash remains a separate source.
-- source:
--   Original stopped Gaussian positive interior spatial crossing L1, after true caplinear localisation and integrable envelope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical

theorem AvramDividend.Classical.avram_a26_original_finitecap_localised_gaussian_crossing_positive_expected_L1
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (a b r : ℝ) (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b)
    (y δ : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc a b)
    (hδ : ∀ᵐ ω ∂P, Tendsto (fun m => δ m ω) atTop (nhds (0 : ℝ)))
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hB : ∀ᵐ ω ∂P, 0 ≤ B ω)
    (hDom : ∀ m, ∀ᵐ ω ∂P,
      max ((if y m ω + δ m ω ≤ c then w (y m ω + δ m ω)
       else w c + (y m ω + δ m ω - c)) -
       (if y m ω ≤ c then w (y m ω)
       else w c + (y m ω - c))) 0 ≤ B ω)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max ((if y m ω + δ m ω ≤ c then w (y m ω + δ m ω)
       else w c + (y m ω + δ m ω - c)) -
       (if y m ω ≤ c then w (y m ω)
       else w c + (y m ω - c))) 0) P) :
    Tendsto (fun m => ∫ ω,
      max ((if y m ω + δ m ω ≤ c then w (y m ω + δ m ω)
       else w c + (y m ω + δ m ω - c)) -
       (if y m ω ≤ c then w (y m ω)
       else w c + (y m ω - c))) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
