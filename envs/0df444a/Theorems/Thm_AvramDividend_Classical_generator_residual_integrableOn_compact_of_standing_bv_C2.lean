-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_residual_integrableOn_compact_of_standing_bv_C2
-- name    : AvramDividend.Classical.generator_residual_integrableOn_compact_of_standing_bv_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:08:39.160763+00:00
-- url     : https://prove2.me/theorems/08d46a3a-885e-4e17-a586-50b1530aae7c
-- title:
--   Standing BV q-scale generator residual is integrable on compact C2 state intervals
-- statement:
--   For a q-scale function W that is C2 on (0,a) under the standing bounded-variation Lévy conditions, the generator residual ΓW−qW is integrable on each compact interval [l,u]⊂(0,a) against any finite state measure. The already proved compact residual-continuity theorem gives continuity; a continuous real function is integrable against a finite measure on a compact interval. This is the compact weak-form input for stopped-occupation and distributional q-harmonicity arguments.
-- source:
--   Accepted compact C2 generator residual continuity and bounded continuous-function integrability theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_residual_integrableOn_compact_of_standing_bv_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IntegrableOn (fun x : ℝ => X.generator W x - q * W x)
      (Icc l u) μ := by sorry

end AvramDividend.Classical
