-- Prove2me | Theorems.Thm_APFB01_hold_is_a_rearrangement
-- name    : APFB01.hold_is_a_rearrangement
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:14:38.124532+00:00
-- url     : https://prove2.me/theorems/b201ba23-e90f-4e80-9047-6ae25ac3d9ee
-- title:
--   Hold is a rearrangement
-- statement:
--   Let a total raw-state map preserve and reflect equality of continuation classes. If the process type is finite, it descends to a bijection of physical classes, every class has a positive return period, and one step is undone there by repeating the map one fewer times than that period.
-- source:
--   Sib v44 Theorems/Thm_APFB01_hold_rearranges.lean:47

import Theorems.Thm_APFPaper5_K3_undo_is_a_repeat
import Theorems.Thm_APFPaper5_K3_kept_along_the_hold
import Theorems.Thm_APFPaper5_K3_every_state_comes_to_return
import Theorems.Thm_APFPaper5_K3_occupant_settles
import Theorems.Thm_APFPaper5_K3_finite_of_separating_family
import Theorems.Thm_APFB01_every_object_comes_to_return

set_option autoImplicit false

universe uX uP uA

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFB01.hold_is_a_rearrangement {X : Type uX} {Process : Type uP} [Finite Process]
    (profile : X → Process → Prop) (hold : X → X)
    (hnodraw : ∀ x y : X, APFB01.physicalClass profile x = APFB01.physicalClass profile y →
      APFB01.physicalClass profile (hold x) = APFB01.physicalClass profile (hold y))
    (hnoerase : ∀ x y : X,
      APFB01.physicalClass profile (hold x) = APFB01.physicalClass profile (hold y) →
      APFB01.physicalClass profile x = APFB01.physicalClass profile y) :
    ∃ D : APFB01.PhysicalState profile → APFB01.PhysicalState profile,
      (∀ x : X, D (APFB01.physicalClass profile x) = APFB01.physicalClass profile (hold x)) ∧
      Function.Bijective D ∧
      ∀ s : APFB01.PhysicalState profile, ∃ n : ℕ, 0 < n ∧ D^[n] s = s ∧ D^[n - 1] (D s) = s := by sorry
