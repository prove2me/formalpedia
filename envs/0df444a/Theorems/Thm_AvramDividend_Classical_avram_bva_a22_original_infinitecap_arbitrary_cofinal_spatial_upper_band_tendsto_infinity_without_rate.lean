-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_infinitecap_arbitrary_cofinal_spatial_upper_band_tendsto_infinity_without_rate
-- name    : AvramDividend.Classical.avram_bva_a22_original_infinitecap_arbitrary_cofinal_spatial_upper_band_tendsto_infinity_without_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:49:56.885837+00:00
-- url     : https://prove2.me/theorems/2cd0fa85-1373-4203-86c9-27beb56c8480
-- title:
--   Original arbitrary cofinal infinite-cap upper spatial bands tend to plus infinity without nesting or spatial-physical rate
-- statement:
--   For the original dividend model with genuinely infinite dividend cap and any supplied spatial bands a_n,b_n satisfying the exact arbitrary cofinal coverage hypothesis for all positive finite reserves, prove that the original upper endpoints b_n tend to positive infinity as the band index grows. For any real M choose the positive interior reserve y=max(1,M+1), which lies below infinite cap and exceeds M. The source cofinal coverage eventually places y inside the original band, giving b_n>=y>=M for all later indices. This establishes the true infinite-cap tail localisation without selecting a faster spatial diagonal, requiring band nesting or coupling band growth to the physical uniform grid refinement. Alongside the finite-cap analogue it supplies the cap-side source tail exhaustion needed by BVA96.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_infinitecap_arbitrary_cofinal_spatial_upper_band_tendsto_infinity_without_rate
    (C : ℝ≥0∞) (hTop : C = ⊤)
    (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    Tendsto b atTop atTop := by sorry
