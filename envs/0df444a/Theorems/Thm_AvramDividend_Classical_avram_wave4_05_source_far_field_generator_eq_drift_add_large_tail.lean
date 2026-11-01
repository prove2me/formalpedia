-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_generator_eq_drift_add_large_tail
-- name    : AvramDividend.Classical.avram_wave4_05_source_far_field_generator_eq_drift_add_large_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:53:22.821805+00:00
-- url     : https://prove2.me/theorems/9350bae0-f0a8-45d0-afad-18c285a5aab2
-- title:
--   Exact full source generator formula: drift plus uncompensated large negative-jump tail beyond cstar+1
-- statement:
--   At all reserves x≥cstar(W)+1, the genuine source Lévy generator is well-defined and equals exactly its drift coefficient c plus the ordinary large-negative-jump integral of vcstar(x+y)−vcstar(x) over y≤−1. The small compensated-jump part cancels because vcstar is affine at x and x+y. The Gaussian term vanishes there since the barrier continuation has zero second derivative; the drift derivative equals 1. Large jumps crossing below ruin remain fully included.
-- source:
--   Accepted full-source above-barrier drift-plus-jump identity and the exact original compensated-integral large-tail theorem, both under source GeneratorIntegrable.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_generator_above_eq_drift_add_jump
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_jump_integral_exact_large_tail

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_far_field_generator_eq_drift_add_large_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x =
        X.c + ∫ y in Iic (-1 : ℝ),
          (vcstar W (x + y) - vcstar W x) ∂X.ν := by sorry
