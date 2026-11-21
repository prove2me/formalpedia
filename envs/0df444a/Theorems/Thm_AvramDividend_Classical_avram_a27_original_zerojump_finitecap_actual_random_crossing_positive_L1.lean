-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_zerojump_finitecap_actual_random_crossing_positive_L1
-- name    : AvramDividend.Classical.avram_a27_original_zerojump_finitecap_actual_random_crossing_positive_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:18:22.968189+00:00
-- url     : https://prove2.me/theorems/d4ebc449-a723-4497-9f2c-dc7d6016156c
-- title:
--   Actual original stopped zerojump finitecap Gaussian cap-crossing positive spatial expected error vanishes
-- statement:
--   Use exact same original spectrally negative Lévy Gaussian X and actual random physical crossing clocks s_m,t_m with bounded horizon and shrinking clock gap, positive-compact reserve Y_m∈[a,b], original HJB candidate w and finitecap V, and integrable majorant of the original spatial correction. Then E[max(V(Y_m+X(t_m)−X(s_m))−V(Y_m),0)]→0. Proved a27 actual Gaussian random crossing increment→0 plus a26 caplinear moving-base dominated convergence yields this result without substituting false full-grid clipping or raw above-cap w. This closes an authentic localised physical finitecap crossing L1 component; ruin and noncompact strips remain separate.
-- source:
--   Original zerojump actual physical Gaussian finitecap caplinear random stop crossing expected L1. Sources: proved actual X increment and localized caplinear dominated convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_zerojump_finitecap_actual_random_crossing_positive_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Set.Icc 0 T ∧ t m ω ∈ Set.Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (a b r : ℝ) (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b)
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc a b)
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hB : ∀ᵐ ω ∂P, 0 ≤ B ω)
    (hDom : ∀ m, ∀ᵐ ω ∂P,
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       (if y m ω ≤ c then w (y m ω)
       else w c + (y m ω - c))) 0 ≤ B ω)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       (if y m ω ≤ c then w (y m ω)
       else w c + (y m ω - c))) 0) P) :
    Tendsto (fun m => ∫ ω,
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       (if y m ω ≤ c then w (y m ω)
       else w c + (y m ω - c))) 0 ∂P)
       atTop (nhds (0 : ℝ)) := by sorry
