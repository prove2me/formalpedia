-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_generatorIntegrand_crossing
-- name    : AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_crossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:28:35.768605+00:00
-- url     : https://prove2.me/theorems/570d4d46-8294-4854-96c1-4c7882b51b6d
-- title:
--   Exact source compensated primitive kernel on strict boundary-crossing jumps
-- statement:
--   For a genuine q-scale W and its oriented primitive U, a strictly small negative jump -r with 0<r<1 crossing below zero from 0<x<r produces the exact original Levy compensated generator integrand r W(x)-U(x). This includes the true derivative compensation: U'=W at positive reserves, U(x-r)=0 below zero. The strict r<1 is essential because the source truncation 1_{(-1,1)} excludes y=-1 and the Levy measure may have an atom there.
-- source:
--   Avram, Palmowski and Pistorius (2007), source Lévy generator in Lemma 4. Uses accepted primitive support and derivative plus exact negative-jump reflection 87cd84ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_crossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r x : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hx0 : 0 < x) (hxr : x < r) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r) =
        r * W x - ∫ t in (0 : ℝ)..x, W t := by sorry
