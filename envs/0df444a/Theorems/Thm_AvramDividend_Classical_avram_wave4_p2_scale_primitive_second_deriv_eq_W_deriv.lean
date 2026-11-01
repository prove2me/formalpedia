-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_second_deriv_eq_W_deriv
-- name    : AvramDividend.Classical.avram_wave4_p2_scale_primitive_second_deriv_eq_W_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:55:30.786249+00:00
-- url     : https://prove2.me/theorems/b80c9317-d2b1-4844-807b-57185f710051
-- title:
--   Second derivative of original q-scale primitive equals the scale derivative
-- statement:
--   For a genuine source Lévy q-scale W, its integral primitive U has U'(z)=W(z) on positive reserves. The derivative equality holds on every positive open neighbourhood of x>0, so differentiating the two locally equal functions gives U''(x)=W'(x), expressed in canonical iteratedDeriv 2 form. This is the exact curvature identification needed to instantiate the Proved weighted triangular kernel theorem for the true primitive's compensated generator jump kernel.
-- source:
--   Avram, Palmowski and Pistorius (2007), original q-scale primitive; accepted FTC theorem a286d355 and pinned Mathlib eventually-equal derivative identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_scale_primitive_second_deriv_eq_W_deriv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) :
    iteratedDeriv 2 (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x =
      deriv W x := by sorry
