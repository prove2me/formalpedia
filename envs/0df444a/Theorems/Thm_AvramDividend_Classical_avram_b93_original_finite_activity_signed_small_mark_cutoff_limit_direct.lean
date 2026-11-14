-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b93_original_finite_activity_signed_small_mark_cutoff_limit_direct
-- name    : AvramDividend.Classical.avram_b93_original_finite_activity_signed_small_mark_cutoff_limit_direct
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T14:22:13.715419+00:00
-- url     : https://prove2.me/theorems/ab1d6d01-819a-4068-a66a-b7901198ddd8
-- title:
--   Finite original negative jump activity gives direct signed first-moment cutoff convergence by domination
-- statement:
--   The original Lévy measure has finite total negative mass under finite negative activity. On the original bounded strip (-1,0), the signed first moment is integrable because |z|<=1. The finite-band source moment integrates z over (-1,-1/(n+1)], and its indicator converges pointwise to one on (-1,0); its absolute value is dominated by |z|. Dominated convergence for the original restricted Lévy measure proves convergence to the full negative strip moment. The first-moment proof is included inside the theorem so no unresolved B83 dependency or global negative-mark second moment is imported.
-- source:
--   Original Lévy measure, restricted first moment and dominated convergence; Avram Palmowski Pistorius (2007) Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Direct source proof: finite negative activity bounds small mark first moment and its signed cutoff moments converge. -/

theorem AvramDividend.Classical.avram_b93_original_finite_activity_signed_small_mark_cutoff_limit_direct
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    Tendsto (fun n : ℕ =>
      ∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)
      atTop (𝓝 (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) := by sorry
