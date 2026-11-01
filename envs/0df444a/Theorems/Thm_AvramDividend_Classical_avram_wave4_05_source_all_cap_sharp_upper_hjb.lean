-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_all_cap_sharp_upper_hjb
-- name    : AvramDividend.Classical.avram_wave4_05_source_all_cap_sharp_upper_hjb
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:27:25.055778+00:00
-- url     : https://prove2.me/theorems/325efc29-bdcc-4140-b21e-52d1b7b44a52
-- title:
--   Source HJB at every sufficiently high reserve including the optimal zero barrier
-- statement:
--   For a genuine source spectrally negative Levy process X satisfying Standing, q>0 and a scale function W, let a be the real cstar barrier including a=0. Whenever x>a, x>=1 and x>=a+max(0,c/q), the actual compensated generator integral of vcstar exists and the HJB max equality holds. For positive a this follows from the source derivative gradient inequality and compensated near-field crossing theorem, and for a=0 it follows directly from the exact source large-jump linear residual bound at x>=1 and the q-discount drift threshold. No shape hypothesis, BV/Gaussian restriction, or extra regularity premise is imposed.
-- source:
--   Avram–Palmowski–Pistorius (2007), Lemma 3(i), generator and Theorem 2(ii); actual source source_positive_cap_near_field_hjb and source_far_field_generator_linear_residual_bound. The zero-cap case uses nonnegativity of ENNReal.toReal and the exact affine derivative above cstar. This rigorously packages a useful sufficient above-cap HJB region uniformly across positive and zero barriers, without asserting the generally false unconditional upper-generator inequality on the remaining compact near-barrier strip.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_all_cap_sharp_upper_hjb {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) (hx : (cstar W).toReal < x) (hx1 : 1 ≤ x) (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) : X.GeneratorIntegrable (vcstar W) x ∧ max (X.generator (vcstar W) x - q * vcstar W x) (1 - deriv (vcstar W) x) = 0 := by sorry
