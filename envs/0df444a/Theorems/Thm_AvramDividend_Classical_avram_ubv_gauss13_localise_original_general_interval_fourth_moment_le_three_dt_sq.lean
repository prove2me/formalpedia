-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_general_interval_fourth_moment_le_three_dt_sq
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_general_interval_fourth_moment_le_three_dt_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:26:57.644452+00:00
-- url     : https://prove2.me/theorems/be3f4cbc-05c1-4346-89d9-953fb9c58ec2
-- title:
--   Original centred Gaussian increment fourth moment scales with squared deterministic interval length
-- statement:
--   For the original ν=0 Lévy source, centred increments over every deterministic interval [s,t] have fourth normalised nonnegative moment at most three times (t-s)^2. The source-exact proof transfers the original stationary increment IdentDistrib law through the measurable fourth-power normalisation and applies the fixed-horizon theorem. This supplies exactly the large-increment quadratic-energy tail estimate on deterministic Gaussian grids needed by compact C² Taylor physical stopped L¹ convergence.
-- source:
--   Public Proved d8a0cca3 original centred increment IdentDistrib, plus quantitative normalised fixed-horizon source bound 61114546 (once Proved), and pinned IdentDistrib.comp/lintegral_eq.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_centred_increment_identdistrib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_fourth_moment_le_three_time_sq

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_general_interval_fourth_moment_le_three_dt_sq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hMeas : Measurable (fun ω : Ω =>
      (X.X (t - s) ω - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ)) :
    (∫⁻ ω, ENNReal.ofReal
      ((((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ) ^ 4) ∂P) ≤
    ENNReal.ofReal (3 * (((t - s : ℝ≥0) : ℝ) ^ 2)) := by sorry
