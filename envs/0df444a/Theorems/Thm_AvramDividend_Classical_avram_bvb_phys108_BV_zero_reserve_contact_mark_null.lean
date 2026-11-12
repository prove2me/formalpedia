-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys108_BV_zero_reserve_contact_mark_null
-- name    : AvramDividend.Classical.avram_bvb_phys108_BV_zero_reserve_contact_mark_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:26:36.109935+00:00
-- url     : https://prove2.me/theorems/b95614be-1c3e-4c9f-864b-60c470869901
-- title:
--   Original BV jump marks hitting zero reserve form a null singleton
-- statement:
--   For any initial reserve level a, the negative-jump mark that makes the post-jump reserve exactly zero has Levy-measure mass zero under the original Standing and bounded-variation assumptions. This supplies the exceptional-set control for markwise compensation limits.
-- source:
--   Original BV compensator-quadrature phys95, via Proved original-standing atomlessness phys107

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys108_BV_zero_reserve_contact_mark_null {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing) (hBV : X.BoundedVariation) (a : ℝ) : X.ν {z : ℝ | a + z = 0} = 0 := by sorry
