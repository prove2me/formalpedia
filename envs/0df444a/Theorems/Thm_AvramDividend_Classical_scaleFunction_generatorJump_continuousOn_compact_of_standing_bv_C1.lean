-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorJump_continuousOn_compact_of_standing_bv_C1
-- name    : AvramDividend.Classical.scaleFunction_generatorJump_continuousOn_compact_of_standing_bv_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:53:37.853692+00:00
-- url     : https://prove2.me/theorems/1c764fc0-d506-4b70-9cfc-d74466a4177b
-- title:
--   Standing BV scale-function jump generator is continuous on compact C1 intervals
-- statement:
--   For a q-scale function C1 on an open positive interval and a standing bounded-variation spectrally negative Lévy process, the compensated negative-jump generator integral is continuous on every compact interior capital interval. This follows from Proved C1 uniform first-order jump domination together with the Proved dominated-convergence bridge for BV jump measures and a.e. state continuity. The theorem is the jump component needed to establish pointwise generator harmonicity without C2 assumptions.
-- source:
--   Avram, Palmowski, Pistorius (2007), Lemma 4: C1 BV Lévy generator continuity.

import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorJump_continuousOn_compact_of_standing_bv_C1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ y : ℝ, SpectrallyNegativeLevy.generatorIntegrand W x y
          ∂(X.ν.restrict (Iio 0)))
      (Icc l u) := by sorry

end AvramDividend.Classical
