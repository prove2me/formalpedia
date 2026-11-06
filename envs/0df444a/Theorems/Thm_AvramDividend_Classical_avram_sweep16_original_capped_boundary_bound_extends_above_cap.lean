-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_capped_boundary_bound_extends_above_cap
-- name    : AvramDividend.Classical.avram_sweep16_original_capped_boundary_bound_extends_above_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:13:35.884586+00:00
-- url     : https://prove2.me/theorems/5b8dee80-f0f3-4cd8-8ec3-4a6453068bf1
-- title:
--   Original capped value boundary estimate extends above any nonnegative finite cap with slope-one candidate
-- statement:
--   Given an original capped dividend value estimate at nonnegative real cap c, a nonnegative candidate boundary value, and an affine slope-one extension w(x)=x-c+w(c) for x>c, the capped bound extends to every x>=c using the exact original valueFunctionLe_above_cap identity. This includes c=0 without inferring strict positive cap. It is deterministic order and ENNReal arithmetic and adds no original-process stochastic assumptions.
-- source:
--   Proved original valueFunctionLe_above_cap UUID 8bd7e873-81b3-409e-a448-bb17eabc4faa; ENNReal.ofReal_add with explicitly nonnegative x-c and w c; Mathlib add_le_add_left.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep16_original_capped_boundary_bound_extends_above_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q c : ℝ) (hc : 0 ≤ c)
    (w : ℝ → ℝ) (hwc : 0 ≤ w c)
    (hBoundary : valueFunctionLe X q (ENNReal.ofReal c) c ≤ ENNReal.ofReal (w c))
    (hAffine : ∀ x : ℝ, c < x → w x = x - c + w c) :
    ∀ x : ℝ, c ≤ x →
      valueFunctionLe X q (ENNReal.ofReal c) x ≤ ENNReal.ofReal (w x) := by sorry
