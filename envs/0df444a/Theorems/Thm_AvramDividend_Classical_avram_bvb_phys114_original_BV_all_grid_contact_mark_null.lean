-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys114_original_BV_all_grid_contact_mark_null
-- name    : AvramDividend.Classical.avram_bvb_phys114_original_BV_all_grid_contact_mark_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:53:16.148661+00:00
-- url     : https://prove2.me/theorems/2d0cf893-82a2-4018-a71f-39844966c6e7
-- title:
--   All original BV two-index grid mark contacts are Levy-null
-- statement:
--   For every original process under Standing and bounded variation, the negative jump marks that exactly cancel any of the countably many grid reserve samples a(n,i) form a Levy-null set. This removes the grid-cell zero-ruin contact discontinuities simultaneously for all mesh refinements in original phys95.
-- source:
--   Original BV phys95 grid contact exceptions; Proved phys111 countable mark nullity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys114_original_BV_all_grid_contact_mark_null {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing) (hBV : X.BoundedVariation) (a : ℕ → ℕ → ℝ) : X.ν {z : ℝ | ∃ n i : ℕ, a n i + z = 0} = 0 := by sorry
