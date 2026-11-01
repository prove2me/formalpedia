-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_jump_part_exact
-- name    : AvramDividend.Classical.avram_wave4_05_source_positive_jump_part_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:44:47.117263+00:00
-- url     : https://prove2.me/theorems/55bc709f-5a01-4826-ad31-f022901769e0
-- title:
--   Exact positive part of the true compensated Levy jump kernel at any upper reserve
-- statement:
--   For the genuine source compensated Levy generator at a reserve x above a positive optimal dividend cap, the positive part of the jump integrand is exactly the positive part of the overshoot defect -vcstar(x)-y for strict small ruin-crossing jumps -1<y<-x, and is zero outside that strip. This is an exact pointwise identity for every negative jump y, including boundary cases. The source derivative at x is exactly one; jumps into negative reserve give post-jump value zero; all other jumps have nonpositive integrand by the source support theorem. It isolates the entire possible positive compensated jump mass to a finite-measure region bounded away from zero for each fixed x>0, without assuming a first moment of the Levy measure.
-- source:
--   Original Avram–Palmowski–Pistorius (2007) fully compensated spectrally negative Levy generator, actual source barrierValue negative extension, derivative one above cstar and source_positive_jump_kernel_support. This creates an exact integrability/overshoot interface for bounded near-barrier generator estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_positive_jump_part_exact {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hpos : 0 < (cstar W).toReal) (x : ℝ) (hx : (cstar W).toReal < x) (y : ℝ) (hy : y < 0) : max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) = if y ∈ Ioo (-1 : ℝ) (-x) then max 0 (-vcstar W x - y) else 0 := by sorry
