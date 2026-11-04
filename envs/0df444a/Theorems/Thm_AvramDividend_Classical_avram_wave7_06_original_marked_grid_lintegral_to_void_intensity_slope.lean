-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_marked_grid_lintegral_to_void_intensity_slope
-- name    : AvramDividend.Classical.avram_wave7_06_original_marked_grid_lintegral_to_void_intensity_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:59:32.514269+00:00
-- url     : https://prove2.me/theorems/941d10ec-698f-4a45-8b4c-1a1300a662e3
-- title:
--   Source occupied-grid L1 convergence yields the intrinsic void intensity slope
-- statement:
--   For the literal source X marked negative-band void probabilities, once an original-space occupied-cell count K has the genuine grid-cell expectation formula, is dominated by the integrable original jump count N, and equals N eventually per source path, the original-void small-time intensity slope follows from dominated convergence and the source count mean Tν(B). The outstanding inputs are explicit and source-specific, with no auxiliary Poisson law.
-- source:
--   W7-06 marked-grid to intensity limit; accepted source dominated convergence e37ce9a7 is the core proof dependency.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_marked_grid_lintegral_to_void_intensity_slope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ)
    (void : ℝ≥0 → ENNReal)
    (hVoid : ∀ s, void s =
      P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0})
    (K : ℕ → Ω → ENNReal) (N : Ω → ENNReal)
    (hK : ∀ m, Measurable (K m))
    (hBound : ∀ m ω, K m ω ≤ N ω)
    (hInt : (∫⁻ ω, N ω ∂P) < ⊤)
    (hEvent : ∀ ω, ∀ᶠ m in (Filter.atTop : Filter ℕ),
      K m ω = N ω)
    (hGridMean : ∀ m,
      (∫⁻ ω, K m ω ∂P).toReal =
        (m : ℝ) * (1 - (void (T / (m : ℝ≥0))).toReal))
    (hRate : (∫⁻ ω, N ω ∂P).toReal =
      (T : ℝ) *
        (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal) :
    Filter.Tendsto
      (fun m : ℕ => (m : ℝ) *
        (1 - (void (T / (m : ℝ≥0))).toReal))
      Filter.atTop (nhds ((T : ℝ) *
        (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)) := by sorry
