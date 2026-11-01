-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_marked_value_increment_measurable_of_process_measurable
-- name    : AvramDividend.Classical.avram_wave4_04b_marked_value_increment_measurable_of_process_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:28:02.096151+00:00
-- url     : https://prove2.me/theorems/d10494db-9569-4d93-a0d5-719ca43707a4
-- title:
--   Marked jump value increment is product-measurable for arbitrary time-sample source σ-algebra
-- statement:
--   For any real-valued Borel w and pre-jump process U measurable in a chosen time–sample σ-algebra m, the marked increment (t,ω,z)↦w(U(t,ω)+z)−w(U(t,ω)) is measurable in m⊗Borel(ℝ). In particular m may be the actual source filtration's predictable σ-algebra once the Proved left-limit predictability bridge is imported; negative ruin-crossing marks remain included without any differentiability outside the cap interior.
-- source:
--   Product measurable fst and snd, pullback along U, addition, Borel composition with w, subtraction. Intended to be specialised to the actual controlled source process, not a marginal coupling or hypothetical Ito-Meyer axiom.

import Mathlib

open MeasureTheory Set
open scoped NNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_marked_value_increment_measurable_of_process_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (m : MeasurableSpace (ℝ≥0 × Ω))
    (U : ℝ≥0 × Ω → ℝ)
    (hU : Measurable[m] U)
    (w : ℝ → ℝ) (hw : Measurable w) :
    Measurable[m.prod inferInstance]
      (fun z : (ℝ≥0 × Ω) × ℝ =>
        w (U z.1 + z.2) - w (U z.1)) := by
  sorry
