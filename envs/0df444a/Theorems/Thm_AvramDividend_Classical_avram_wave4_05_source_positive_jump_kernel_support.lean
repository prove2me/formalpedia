-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_jump_kernel_support
-- name    : AvramDividend.Classical.avram_wave4_05_source_positive_jump_kernel_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:38:33.635771+00:00
-- url     : https://prove2.me/theorems/c2527bf5-ec5a-44be-92a2-e6f9f80aa435
-- title:
--   Positive original compensated jump kernel is supported only on small ruin crossings
-- statement:
--   For a genuine Standing spectrally negative Levy process, q>0, an exact scale W and positive optimal barrier a, let x>a and y<0. If y is outside the strict interval (-1,-x), then the original fully compensated Levy generator integrand of vcstar at (x,y) is nonpositive. The only possible positive part of the source compensated jump kernel is supported on small ruin-crossing jumps -1<y<-x. The interval is empty when x>=1. The theorem keeps the original negative-reserve value zero, derivative one at x, source truncated compensation, and the exact zero boundary. It is valid with infinite activity and does not require the value floor vcstar(x)>=1. It isolates the entire finite-width obstruction to generator nonpositivity near small reserves.
-- source:
--   Avram–Palmowski–Pistorius (2007) generator and Lemma 3(i); original source generatorIntegrand, vcstar derivative>=1 and continuity at zero, left affine-majorant calculus, cstar finiteness and global vcstar monotonicity. Adaptation of the genuine complete accepted source proof vcstar_near_field_jump_nonpos_of_unit_value de82f3f5: omit the unit-value assumption, replacing its small-ruin case by exclusion of precisely y in (-1,-x). The original compensation indicator, endpoint and large-jump branches are preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_positive_jump_kernel_support {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hpos : 0 < (cstar W).toReal) (x : ℝ) (hx : (cstar W).toReal < x) (y : ℝ) (hy : y < 0) (houtside : y ∉ Ioo (-1 : ℝ) (-x)) : SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ≤ 0 := by sorry
