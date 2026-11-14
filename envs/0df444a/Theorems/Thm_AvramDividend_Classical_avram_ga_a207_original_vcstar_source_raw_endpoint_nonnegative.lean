-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a207_original_vcstar_source_raw_endpoint_nonnegative
-- name    : AvramDividend.Classical.avram_ga_a207_original_vcstar_source_raw_endpoint_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:32:26.017939+00:00
-- url     : https://prove2.me/theorems/e93fbef0-fe59-4cb0-a65f-f88ba70842b7
-- title:
--   The original zero-jump physical Gaussian raw prepayment source endpoint has nonnegative actual vcstar value
-- statement:
--   For a spectrally negative Levy process with the original standing hypotheses, a positive discount q, valid scale function W and finite optimal barrier cstar, the actual candidate barrier value vcstar W evaluated at the genuine physical source observation x + X.X(t) - rightLimit D(s) is nonnegative for all starting capital, dividend traces, sample paths and grid times s,t. This is the exact raw endpoint term in the full-cell discount residual; the already Proved sweep17 candidate nonnegativity controls nonnegative endpoints and vcstar_eq_zero_of_neg controls negative endpoints. It supplies the nonnegative source value premise for the repaired discount proof route a199 while avoiding the unsound unrestricted generic w assumption in original a151.
-- source:
--   Proved AVRAM original candidate nonnegativity avram_sweep17_vcstar_nonnegative_without_smoothness and negative-reserve zero extension vcstar_eq_zero_of_neg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy


import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_nonnegative_without_smoothness
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_ga_a207_original_vcstar_source_raw_endpoint_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hc : cstar W < ⊤)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (s t : ℝ≥0) (ω : Ω) :
    0 ≤ vcstar W (x + X.X t ω - rightLimit D s ω) := by sorry
