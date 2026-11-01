-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_all_cap_positive_jump_part_exact
-- name    : AvramDividend.Classical.avram_wave4_05_source_all_cap_positive_jump_part_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:29:28.160629+00:00
-- url     : https://prove2.me/theorems/7c0f8368-9fc5-4050-adf7-f95f3567f63f
-- title:
--   Exact positive part of the genuine compensated Levy jump kernel for every source optimal cap
-- statement:
--   For every original source spectrally negative Levy process satisfying Standing, q>0, its q-scale function W and the finite optimal dividend cap cstar, at each reserve x strictly above cstar and every negative jump y, the positive part of the true compensated generator integrand is exactly max(0,-vcstar(x)-y) on the strict small ruin-crossing strip -1<y<-x and is zero everywhere else. This includes the zero-barrier and positive-barrier cases, all compensation and ruin boundary terms, with no additional Gaussian, bounded-variation, C2 or finite Levy first-moment assumption.
-- source:
--   Avram Palmowski Pistorius 2007 generator, accepted positive- and zero-optimal-cap exact source compensated jump identities and finite cstar.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_all_cap_positive_jump_part_exact {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) (y : ℝ) (hy : y < 0) : max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) = if y ∈ Ioo (-1 : ℝ) (-x) then max 0 (-vcstar W x - y) else 0 := by sorry
