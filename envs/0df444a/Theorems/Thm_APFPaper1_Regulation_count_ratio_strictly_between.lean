-- Prove2me | Theorems.Thm_APFPaper1_Regulation_count_ratio_strictly_between
-- name    : APFPaper1.Regulation.count_ratio_strictly_between
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:29:10.362948+00:00
-- url     : https://prove2.me/theorems/8671e846-5197-4748-a7f0-a2243e6488c6
-- title:
--   A mixed list has positive joint count below individual count
-- statement:
--   Work in a supplied typed-word regulation model with a fragment execution relation, whole-word bills, starting-context capacities and Boolean readings on raw endpoint states. A mark is holdable when some budgeted response has a run reading it true; joint holdability requires both readings true in the same run. Each count retains repeated occurrences in the list. The hypotheses do not follow merely from B06 occupancy, and no continuum of attainable ratios is established. Suppose the supplied list contains x₀ where the pair is jointly holdable, and x₁ where each mark is holdable but the pair is not jointly holdable. Then the jointly-holdable count is positive and strictly smaller than the individually-holdable count. The conclusion concerns these natural-number counts directly, rather than a division or a probability. Source: November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.
-- source:
--   Theorems/Thm_APFPaper1_Regulation_overflow.lean, declaration at line 63 (Sib v15; source-scoped review). November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.

import Theorems.Thm_APFPaper1_Regulation_bothCount_lt_eachCount_of_witness

set_option autoImplicit false
namespace APFPaper1.Regulation
end APFPaper1.Regulation
open APFPaper1.Regulation
open APFPaper1.Continuation
open Classical

universe uC uF uX uR uM
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {M : Type uM}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → WordFrom Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
  (reads : (h : Context) → Raw h → M → Bool)

theorem APFPaper1.Regulation.count_ratio_strictly_between (g : Context) (xs : List (Raw g)) (m1 m2 : M)
    (x0 x1 : Raw g) (hx0 : x0 ∈ xs) (hx1 : x1 ∈ xs)
    (hheld : JointlyHoldable step resource calibration C reads g x0 m1 m2)
    (hirr : IrreduciblyJointAt step resource calibration C reads g x1 m1 m2) :
    0 < bothCount step resource calibration C reads g xs m1 m2 ∧
      bothCount step resource calibration C reads g xs m1 m2 <
        eachCount step resource calibration C reads g xs m1 m2 := by sorry
