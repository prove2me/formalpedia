-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_original_negative_jump_endpoint_fiber_public
-- name    : AvramDividend.Classical.avram_chat24_original_negative_jump_endpoint_fiber_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T14:05:27.453545+00:00
-- url     : https://prove2.me/theorems/881905d2-7eca-4586-8e89-f343d824167d
-- title:
--   Original negative-jump endpoint fiber is its actual source atom
-- statement:
--   Source-faithful original-source ingredient for 7c376a84-b0d3-4cc5-bbcb-57bdc43931aa. The same original X jump counting graph restricted to a positive endpoint consists of the one original jump mark, with zero contribution when that mark is not negative. Actual joint jump-mark measurability supplies the measurable graph. An arbitrary time guard E and signed reward f preserve the concrete compact reserve kernel as a specialization. Published as a public prerequisite because the authoritative parent is public and public candidates cannot import private helper declarations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_chat24_original_negative_jump_endpoint_fiber_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (E : ℝ≥0 → Prop) [DecidablePred E] (f : ℝ≥0 × ℝ → ℝ) :
    let z : ℝ≥0 → ℝ := fun u => X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let NX : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ z u ≠ 0}).map (fun u => (u, z u))
    (∫ p, if p.1 = t ∧ E p.1 ∧ p.2 < 0 then f p else 0 ∂NX) =
      if E t ∧ z t < 0 then f (t, z t) else 0 := by sorry
