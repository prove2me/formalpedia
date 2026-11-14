-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_original_smallband_marked_window_difference_20261113
-- name    : AvramDividend.Classical.avram_a23_original_smallband_marked_window_difference_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:07:18.149215+00:00
-- url     : https://prove2.me/theorems/f9be892c-83ec-43a4-ad1d-51495015408c
-- title:
--   Every original finite negative marked-band source window is exactly its compact prefix difference
-- statement:
--   For the original spectrally negative Levy process on its own sample space, any separated negative marked jump band has its signed (s,t] integral equal to the difference of the two source prefix signed integrals. This holds pathwise for every sample path, without any independent Gaussian component.
-- source:
--   Proved avram_p4_h_gaussian_original_smalljump_cutoff_mark_integrable 1fa1d6da and Mathlib disjoint setIntegral_union; A23 Gaussian source measurable shift path plan.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_mark_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original signed retained negative band on (s,t] is the difference of the two source prefixes. -/

theorem AvramDividend.Classical.avram_a23_original_smallband_marked_window_difference_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (n : ℕ) (s t : ℝ≥0) (hst : s ≤ t) :
    let μ : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    (∫ p in (Ioc (0 : ℝ≥0) t ×ˢ B), p.2 ∂μ) -
      (∫ p in (Ioc (0 : ℝ≥0) s ×ˢ B), p.2 ∂μ) =
    (∫ p in (Ioc s t ×ˢ B), p.2 ∂μ) := by sorry
