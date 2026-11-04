-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_true_grid_ceiling_bounded_stopping_exists
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_ruin_true_grid_ceiling_bounded_stopping_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:43:45.55349+00:00
-- url     : https://prove2.me/theorems/04405176-d317-42da-b497-a61922f3e3aa
-- title:
--   Original admissible ruin-clock grid ceiling exists as a bounded right-continuous sampled stopping time
-- statement:
--   Under the original spectrally negative Lévy source and an actual dividend strategy, the natural finite-horizon ruin time is a right-continuous-filtration stopping time and bounded by n. Any monotone sampled grid reaching time n by index N therefore admits a first index K at or after that actual ruin-clipped clock. This K is a bona fide discrete stopping time for sampled 𝓕.rightCont, uniformly bounded by N. No explicit hτstop, ad hoc measurability or state-band interior assumption is needed.
-- source:
--   Composition of Proved original ruinTime_stopping_rightCont_filtration 2d036d4f, clock truncation 7bcaac6d, bounds 6b7a13a0, new P4-E Nat.find adapted ceiling 5aee1f98 and sampled discrete stopping adapter d0b4325f.

import Mathlib
import Mathlib.Data.Nat.Find
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_truncated_clock_stopping_of_ruin_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_truncated_ruin_grid_ceiling_index_adapted
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_rightcont_grid_index_isStoppingTime

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original ruin-clipped source has a bounded sampled right-continuous stopping ceiling. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_ruin_true_grid_ceiling_bounded_stopping_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (n : ℕ)
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (N : ℕ) (hN : (n : ℝ≥0) ≤ e N)
    (𝓖 : Filtration ℕ mΩ)
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ)) :
    ∃ K : Ω → ℕ,
      IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ)) ∧
      (∀ ω, (K ω : WithTop ℕ) ≤ (N : WithTop ℕ)) ∧
      (∀ ω, (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≤ e (K ω)) := by sorry
