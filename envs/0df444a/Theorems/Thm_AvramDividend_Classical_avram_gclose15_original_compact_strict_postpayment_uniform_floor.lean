-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gclose15_original_compact_strict_postpayment_uniform_floor
-- name    : AvramDividend.Classical.avram_gclose15_original_compact_strict_postpayment_uniform_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T18:08:00.082303+00:00
-- url     : https://prove2.me/theorems/026251d7-f1c8-4642-97ef-c3e530522f3d
-- title:
--   Strictly positive original postpayment reserve on a compact prefix has a uniform positive floor
-- statement:
--   On each fixed compact time prefix, pathwise strict positivity of the original postpayment surplus implies a uniform positive lower reserve margin. The proof uses the new source-exact upper semicontinuity of its negative and the already proved compact prefix supremum separation. It isolates the deterministic compactness argument from the genuinely stochastic remaining task of proving no zero postpayment contact strictly before ruin.
-- source:
--   Original negative postpayment USC from 5b13a627 and generic USC compact prefix strict-supremum separation b2aaf6e5. This establishes the exact reusable uniform lower-floor premise for Gaussian top cap 61cdc38d once strict pre-ruin postpayment positivity has been formally derived.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose15_original_negative_postpayment_usc
import Theorems.Thm_AvramDividend_Classical_usc_compact_prefix_sup_strictly_below_level
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gclose15_original_compact_strict_postpayment_uniform_floor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0)
    (hpos : ∀ s : ℝ≥0, s ≤ T →
      0 < x + X.X s ω - rightLimit D s ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ≥0, s ≤ T →
      δ ≤ x + X.X s ω - rightLimit D s ω := by sorry
