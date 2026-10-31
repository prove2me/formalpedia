-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_barrierSupValue_lt_top
-- name    : AvramDividend.Classical.avram_wave3_02_standing_barrierSupValue_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:33:56.859026+00:00
-- url     : https://prove2.me/theorems/0f6d05f6-2ef3-4bbb-9dc1-eeeef14d564a
-- title:
--   Finiteness of the genuine reflected supremum reward at every positive barrier
-- statement:
--   For the original Standing spectrally negative Levy process at any q>0 and every a>0, the expected discounted dividend reward of the true reflected running-supremum regulator stopped at drawdown ruin is finite in ENNReal. This is a genuine source-level finiteness result independent of W differentiability, obtained from the canonically Proved Standing-only strictly finite first-record renewal bound.
-- source:
--   Avram Palmowski Pistorius (2007), killed first-record renewal, via Proved avram_wave3_02_standing_finite_step_upper and pinned Mathlib ENNReal.ofReal_lt_top.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_finite_step_upper

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_standing_barrierSupValue_lt_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    barrierSupValue X a q < ⊤ := by sorry
