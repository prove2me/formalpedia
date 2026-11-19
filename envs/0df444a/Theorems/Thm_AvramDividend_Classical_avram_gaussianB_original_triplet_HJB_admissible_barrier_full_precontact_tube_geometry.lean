-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_triplet_HJB_admissible_barrier_full_precontact_tube_geometry
-- name    : AvramDividend.Classical.avram_gaussianB_original_triplet_HJB_admissible_barrier_full_precontact_tube_geometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T07:24:42.186742+00:00
-- url     : https://prove2.me/theorems/0d153975-618d-4265-92c7-951e1968c1ab
-- title:
--   Original HJB-admissible barrier source has exact Lévy triplet c=2, sigma=1, nu=0 and full positive precontact Gaussian tube geometry
-- statement:
--   For any strictly positive physical horizon T, the actual spectrally negative Gaussian Lévy source with c=2, sigma=1, nu=0 has exact drift-two Brownian sample paths, Standing and unbounded variation, an admissible equal-cap barrier strategy, and on every small source tube an exact lower-band first-contact horizon T, precontact reserve above 5/44 and terminal reserve at most 1/8. This retains the true source triplet omitted from earlier B51 witness packaging, allowing the physical occupation term in the original B52 proof to be identified as max Y.c 0 × Occ rather than an unrelated constant coefficient.

import Mathlib.Tactic.NormNum
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB132_original_positive_gaussian_standing_witness_with_exact_path
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_original_barrier_no_initial_atom_source
import Theorems.Thm_AvramDividend_Classical_avram_gbB38_barrier_reserve_above_cutoff_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_short_barrier_terminal_reserve_le_cap
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_original_triplet_HJB_admissible_barrier_full_precontact_tube_geometry
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (Y : SpectrallyNegativeLevy gaussianLimit 𝓕),
      (∀ (t : ℝ≥0) (ω : ℝ≥0 → ℝ),
        Y.X t ω = brownian t ω - brownian 0 ω + 2 * (t : ℝ)) ∧
      Y.c = 2 ∧ Y.σ = 1 ∧ Y.ν = 0 ∧
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
