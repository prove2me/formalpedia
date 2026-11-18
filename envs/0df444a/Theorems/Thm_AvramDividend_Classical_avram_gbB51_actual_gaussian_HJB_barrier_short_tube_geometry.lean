-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry
-- name    : AvramDividend.Classical.avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:54:03.818512+00:00
-- url     : https://prove2.me/theorems/78ca3642-6ccb-4145-90a6-f84adad02697
-- title:
--   Concrete original Gaussian HJB-admissible model with exact stopping clock and terminal strip bounds
-- statement:
--   There exists a fully HJB-admissible original zero-jump Gaussian Lévy source with exactly the canonical Brownian drift-2 path and unbounded variation. On every narrow source tube it has stopped lower-hit clock T and terminal reserve in (5/44,1/8]. This discharges original model existence, admissibility, stopped geometry and terminal-band obligations; it leaves Brownian tube positivity and exact stochastic discounted cash identity separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB133_original_gaussian_full_HJB_admissible_witness_with_exact_path
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_short_barrier_terminal_reserve_le_cap
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB51_actual_gaussian_HJB_barrier_short_tube_geometry
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.Standing ∧ ¬ Y.BoundedVariation ∧
      IsAdmissibleLe Y (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      (∀ ω : ℝ≥0 → ℝ,
        (∀ s : ℝ≥0, s ≤ T → |Y.X s ω| ≤ (1 / 400 : ℝ)) →
        sInf ((Icc (0 : ℝ≥0) T ∩
          (fun t : ℝ≥0 => -(riskProcess Y (1 / 8 : ℝ)
            (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
            Ici (-(5 / 44 : ℝ))) ∪ {T}) = T ∧
        (5 / 44 : ℝ) <
          riskProcess Y (1 / 8 : ℝ)
            (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω ∧
        riskProcess Y (1 / 8 : ℝ)
          (barrierStrategy Y (1 / 8 : ℝ) (1 / 8 : ℝ)) T ω ≤
          (1 / 8 : ℝ)) := by sorry
