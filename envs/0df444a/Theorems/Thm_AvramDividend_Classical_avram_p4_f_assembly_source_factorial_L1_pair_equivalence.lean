-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_source_factorial_L1_pair_equivalence
-- name    : AvramDividend.Classical.avram_p4_f_assembly_source_factorial_L1_pair_equivalence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:05:04.694938+00:00
-- url     : https://prove2.me/theorems/9328a606-81c3-4a9f-89fc-da8eb6eb08af
-- title:
--   Original source factorial L1 and expectation reduce exactly to genuine ordered jump pairs
-- statement:
--   On the same original spectrally negative Levy source X and any finite negative cutoff, integrability of the real factorial random jump count N(N−1) is equivalent to integrability of twice the count of strictly time-ordered genuine source jump pairs, and their Bochner expectations agree. The equality is source-exact and needs no Poisson assumption or extra second moment. It isolates the remaining probabilistic pair-moment bound needed to use P4-B original finite-band L² variance.
-- source:
--   Accepted public Proved original real chronological pair factorial identity 074f945f, pathwise finite source marked times e5e6f70b. This converts—not assumes—P4-B genuine source L1 factorial moment to ordered-pair energy.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_real_factorial_pair
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_source_factorial_L1_pair_equivalence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let J : Ω → ℝ := fun ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    (Integrable (fun ω => J ω * (J ω - 1)) P ↔
      Integrable (fun ω => 2 * (K ω : ℝ)) P) ∧
    (∫ ω, J ω * (J ω - 1) ∂P) =
      (∫ ω, 2 * (K ω : ℝ) ∂P) := by sorry
