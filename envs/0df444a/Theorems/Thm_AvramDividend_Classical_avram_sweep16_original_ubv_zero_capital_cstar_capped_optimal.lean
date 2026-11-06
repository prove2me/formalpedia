-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_zero_capital_cstar_capped_optimal
-- name    : AvramDividend.Classical.avram_sweep16_original_ubv_zero_capital_cstar_capped_optimal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:49:25.239575+00:00
-- url     : https://prove2.me/theorems/90146681-4fa1-41fa-9734-c3c78dd63759
-- title:
--   Exact capped optimal barrier at zero initial reserve for the original unbounded-variation Lévy process
-- statement:
--   Original spectrally negative Lévy dividend-control theorem. For a genuinely unbounded-variation process under standing hypotheses and root smoothing, at x=0 the c-star barrier achieves the exact capped optimum. At zero threshold, use Proved zero-cap original optimality. At positive threshold, combine source-exact regularity and HJB under cap with the Proved original UBV zero-start upper, and a genuinely admissible c-star barrier lower. No positive-reserve stochastic budget or equality in law is assumed.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_local_verification_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_start_capped_valueFunctionLe_upper
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_enlarged_cap_barrier_lower
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_zero_cstar_original_capped_optimality

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_ubv_zero_capital_cstar_capped_optimal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : ¬ X.BoundedVariation)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    valueFunctionLe X q (cstar W) 0 = ENNReal.ofReal (vcstar W 0) := by sorry
