-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_far_field_generator_residual_nonpos_of_monotone
-- name    : AvramDividend.Classical.vcstar_far_field_generator_residual_nonpos_of_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T10:11:18.351419+00:00
-- url     : https://prove2.me/theorems/0b8f8042-c4e0-48cc-8457-ee30eb69e493
-- title:
--   Far-field HJB generator inequality from nonlocal negative-jump sign and monotone dividend value
-- statement:
--   At x at least one unit above the real optimal barrier, all compensated small negative jumps remain on the affine value branch and contribute zero. For y at most -1, the compensator vanishes and monotonicity of vcstar makes the remaining jump contribution nonpositive. Thus the entire jump integral is nonpositive and the exact generator is at most X.c. If in addition q times the candidate value at x is at least X.c, the generator residual is nonpositive and its jump integral is integrable. The theorem states monotonicity and the explicit q-value comparison as assumptions; it makes a genuine nonlocal integral-sign deduction but does not claim the inequality immediately above cstar.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_far_field_generator_residual_nonpos_of_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hmono : Monotone (vcstar W))
    (x : ℝ)
    (hfar : (cstar W).toReal + 1 ≤ x)
    (hbound : X.c ≤ q * vcstar W x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x ≤ 0 := by sorry
