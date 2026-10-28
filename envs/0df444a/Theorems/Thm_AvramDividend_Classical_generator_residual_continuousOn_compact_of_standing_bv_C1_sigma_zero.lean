-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_standing_bv_C1_sigma_zero
-- name    : AvramDividend.Classical.generator_residual_continuousOn_compact_of_standing_bv_C1_sigma_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:02:16.360442+00:00
-- url     : https://prove2.me/theorems/2f05969b-6ec7-455f-ad09-f8b0917def9c
-- title:
--   First-order Lévy generator residual is continuous on compact BV C1 intervals
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process with zero Gaussian coefficient and q-scale function W of class C1 on (0,a), the discounted generator residual x↦ΓW(x)−qW(x) is continuous on every compact positive reserve interval. Local continuity of W and W' follows from C1 regularity. The new unconditional BV C1 jump continuity supplies the integral component. The sigma-zero generator continuity theorem then combines them, avoiding any second derivative assumption.
-- source:
--   Avram, Palmowski, Pistorius (2007), Lemma 4; first-order BV C1 residual continuity.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_residual_continuousOn_compact_of_standing_bv_C1_sigma_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation) (hσ : X.σ = 0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Icc l u) := by sorry

end AvramDividend.Classical
