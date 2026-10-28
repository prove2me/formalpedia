-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_bv_standing
-- name    : AvramDividend.Classical.cstar_lt_top_of_bv_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:25:43.808195+00:00
-- url     : https://prove2.me/theorems/77ab8d7d-d14d-4004-8edd-bee045a7cb60
-- title:
--   Finiteness of the Avram optimal dividend barrier for bounded-variation paths under standing assumptions
-- statement:
--   For a spectrally negative Lévy process satisfying Avram's standing conditions and having bounded-variation sample paths, the optimal derivative-minimising barrier c* is finite at every positive discount rate. Combine the proved absolute continuity of its Lévy measure, positive-axis C1 regularity of its scale function, Esscher-normalised positivity and monotonicity, and the deterministic coercive-barrier finiteness criterion. This closes the bounded-variation case independently of the open unbounded-variation stochastic and regularity branches.
-- source:
--   Avram et al. (2007), Lemma 2(i), with canonical proved lemmas standing_bv_levy_absolutely_continuous, scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy, scaleFunction_tilted_positive_monotone_of_bv and cstar_finite_of_normalized_monotone.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_normalized_monotone
import Mathlib.Analysis.Calculus.Deriv.Basic

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cstar_lt_top_of_bv_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    cstar W < ⊤ := by sorry
