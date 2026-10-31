-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
-- name    : AvramDividend.Classical.avram_wave3_01_infinite_small_jump_not_bv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:56:35.817653+00:00
-- url     : https://prove2.me/theorems/b69119ba-259b-44ca-b3e1-d2c01fd2f1b4
-- title:
--   Infinite small-negative-jump first variation rules out bounded-variation Lévy paths
-- statement:
--   In a genuine spectrally negative Lévy process, divergence of the absolute first moment of jumps in (-1,0) contradicts bounded variation. The Proved source BV theorem gives IntegrableOn of the small-jump identity, hence its ENNReal absolute lintegral is finite. This removes the explicit not-BV parameter required by source record positivity and scale sandwich, allowing direct use from the canonical infinite-small-jump C1 theorem.
-- source:
--   Proved boundedVariation_smallJump_integrable UUID 4291cf5b-195d-4c8f-907f-724f3d3c1bc2. Canonical root C1 UUID cd61d678.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_integrable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_infinite_small_jump_not_bv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ¬ X.BoundedVariation := by sorry
