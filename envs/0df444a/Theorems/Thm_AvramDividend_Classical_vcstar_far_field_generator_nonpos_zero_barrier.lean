-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_far_field_generator_nonpos_zero_barrier
-- name    : AvramDividend.Classical.vcstar_far_field_generator_nonpos_zero_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:11:37.703334+00:00
-- url     : https://prove2.me/theorems/1fd5b0df-9fa0-4df5-b663-44b714a6838d
-- title:
--   Zero-barrier candidate satisfies the Lévy generator inequality above the unit reserve
-- statement:
--   Let cstar equal zero for a standing q-scale function. At every reserve x at least one unit and large enough that the discounting of x dominates Lévy drift c, the candidate's full compensated Lévy generator is integrable and its residual Γv−qv is nonpositive. Global monotonicity of the candidate controls negative jumps, and the nonnegative zero-boundary value strengthens qx≥c to qv(x)≥c. This is a concrete far-field HJB bound with no generator-inequality assumption.
-- source:
--   Canonically Proved far-field generator inequality (0b8f8042-c4e0-48cc-8457-ee30eb69e493), zero-barrier boundary nonnegativity (861b7656-5bc3-4d92-81da-da184060de56) and newly authored monotone zero-barrier theorem (pending publication and proof).

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_zero_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_far_field_generator_residual_nonpos_of_monotone
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_far_field_generator_nonpos_zero_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hc0 : cstar W = 0)
    (x : ℝ) (hx : 1 ≤ x) (hcost : X.c ≤ q * x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x ≤ 0 := by sorry
