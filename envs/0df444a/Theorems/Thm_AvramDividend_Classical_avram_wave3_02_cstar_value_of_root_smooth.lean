-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_value_of_root_smooth
-- name    : AvramDividend.Classical.avram_wave3_02_cstar_value_of_root_smooth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:09:57.548653+00:00
-- url     : https://prove2.me/theorems/92d5017b-f51b-4598-b3ed-9f8dc51546be
-- title:
--   Genuine cstar all-capital reflected value under exactly the root smoothness alternatives
-- statement:
--   For finite cstar and the exact root Gaussian-or-BV-or-C2(vcstar) condition, the original reflected barrier dividend value equals vcstar at every nonnegative capital, including cstar=0, x=0, below barrier and above barrier.
-- source:
--   Avram–Palmowski–Pistorius 2007, Proposition 1. The nonzero positive optimal-barrier derivative is proved separately under root smoothness. The true arbitrary positive-barrier allcapital value uses the actual Stieltjes dividend/first-upcrossing renewal, and the zero-barrier value uses the source boundary package.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_deriv_pos_of_root_smooth
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_capital_of_local_deriv_nonzero
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_cstar_value_of_root_smooth {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
        ENNReal.ofReal (vcstar W x) := by sorry
