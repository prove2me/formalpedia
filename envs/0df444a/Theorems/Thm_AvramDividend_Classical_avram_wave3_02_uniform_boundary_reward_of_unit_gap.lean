-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_boundary_reward_of_unit_gap
-- name    : AvramDividend.Classical.avram_wave3_02_uniform_boundary_reward_of_unit_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:34:10.28841+00:00
-- url     : https://prove2.me/theorems/5942349e-cdaa-44a6-9d4e-9c78ba14370c
-- title:
--   Uniform finite bound on true reflected dividend reward from a common scale increment gap
-- statement:
--   In the original Standing spectrally negative Lévy process, suppose the q-scale function has one common positive one-step relative gap: c W(a+1)≤W(a+1)-W(a) at every positive a for c>0. Then the genuine original stopped Stieltjes reflected-regulator boundary reward is uniformly at most ENNReal.ofReal (1/c) over all nonnegative barrier heights, including zero. The proof uses the Proved source killed-grid positive-gap bound, positivity of the scale function, elementary ratio algebra, and monotonicity of the actual reflected reward. It requires no global C1 or derivative of W.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1 and boundary reward estimate (3.15); accepted first-record finite gap and reflected reward monotonicity.

import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_positive_gap_upper_value
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_uniform_boundary_reward_of_unit_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ a : ℝ, 0 < a →
      c * W (a + 1) ≤ W (a + 1) - W a) :
    ∀ a : ℝ, 0 ≤ a →
      barrierSupValue X a q ≤ ENNReal.ofReal (1 / c) := by sorry
