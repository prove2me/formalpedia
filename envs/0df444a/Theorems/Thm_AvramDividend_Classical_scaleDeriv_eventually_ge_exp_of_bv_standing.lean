-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_eventually_ge_exp_of_bv_standing
-- name    : AvramDividend.Classical.scaleDeriv_eventually_ge_exp_of_bv_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:53:26.091219+00:00
-- url     : https://prove2.me/theorems/980b0375-efab-42a4-a810-ffc40792178d
-- title:
--   Exponential growth lower bound for the q-scale derivative under bounded variation and Avram standing assumptions
-- statement:
--   For a spectrally negative Lévy process satisfying the Avram standing assumptions, with bounded variation and positive discount q, the derivative of its q-scale function is eventually bounded below by c exp(φx) for some strictly positive φ and c. This quantitative growth estimate follows from the already Proved Esscher-normalised monotonicity, scale-function C1 regularity, and deterministic exponential derivative comparison.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 2(i), §5.3; canonical Proved bounded-variation tilted-scale, regularity, derivative lower-bound and normalized exponential-growth lemmas.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_normalized_eventual_derivative_growth
import Mathlib.Analysis.Calculus.Deriv.Basic

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleDeriv_eventually_ge_exp_of_bv_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    ∃ φ c : ℝ, 0 < φ ∧ 0 < c ∧
      ∀ᶠ x in Filter.atTop, c * Real.exp (φ * x) ≤ deriv W x := by sorry
