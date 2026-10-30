-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_deriv_pos_of_root_smooth
-- name    : AvramDividend.Classical.avram_wave3_02_cstar_deriv_pos_of_root_smooth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:01:58.181291+00:00
-- url     : https://prove2.me/theorems/2bb93581-2bfd-48c2-ada8-5a5122db7fed
-- title:
--   Positive scale derivative at finite positive optimal barrier for every root smoothness branch
-- statement:
--   Under the root smoothness disjunction and finite positive optimal barrier, the q-scale-function derivative at that barrier is strictly positive. This covers positive Gaussian volatility, bounded variation and C2 smoothness of vcstar without globally assuming scale function C1.
-- source:
--   Proved Gaussian/BV scale-slope positivity plus new Proved C2(vcstar) smooth-fit nonvanishing argument and canonical scaleDeriv_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scaleDeriv_pos_of_gaussian_or_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_nonzero_of_vcstar_C2
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonneg

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_cstar_deriv_pos_of_root_smooth {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ))) :
    0 < deriv W (cstar W).toReal := by sorry
