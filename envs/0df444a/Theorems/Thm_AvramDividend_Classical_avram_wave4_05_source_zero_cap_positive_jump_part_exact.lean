-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_zero_cap_positive_jump_part_exact
-- name    : AvramDividend.Classical.avram_wave4_05_source_zero_cap_positive_jump_part_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:27:47.581832+00:00
-- url     : https://prove2.me/theorems/37319805-3f98-4c1c-bbce-bca73b174aab
-- title:
--   Exact positive part of the original compensated Levy generator jump kernel at zero cap
-- statement:
--   For the actual original compensated spectrally negative Levy generator at zero optimal dividend barrier, every positive reserve x and negative jump y, the positive part of the generator integrand is exactly max(0,-vcstar(x)-y) if and only if y lies in the strict small ruin-crossing band -1<y<-x, and is zero otherwise. The equality includes the landing-at-zero boundary and the source compensation convention, using the source zero value below ruin and exact derivative one above cap. No extra Gaussian, BV, C2 or finite first Levy moment assumption is needed.
-- source:
--   Avram Palmowski Pistorius original compensated generator, accepted zero-cap positive-kernel support and original above-cap derivative equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_zero_cap_positive_jump_part_exact {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hc0 : cstar W = 0) (x : ℝ) (hx : 0 < x) (y : ℝ) (hy : y < 0) : max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) = if y ∈ Ioo (-1 : ℝ) (-x) then max 0 (-vcstar W x - y) else 0 := by sorry
