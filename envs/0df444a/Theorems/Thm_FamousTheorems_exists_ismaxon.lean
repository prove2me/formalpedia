-- Prove2me | Theorems.Thm_FamousTheorems_exists_ismaxon
-- name    : FamousTheorems.exists_ismaxon
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:55:05.385397+00:00
-- url     : https://prove2.me/theorems/03985ceb-241b-4fd4-8eea-a397134c984d
-- title:
--   The extreme value theorem (maximum)
-- statement:
--   **The extreme value theorem**, maximum form. A continuous real-valued function on a nonempty compact set attains its maximum. Compactness prevents the supremum from escaping: on an open or unbounded domain a continuous function may approach its supremum without reaching it. Together with the minimum form it says the image of a compact set is a compact interval, and it is the existence result underlying optimisation -- a maximiser exists before any method is applied to find it. **Formalization note.** `IsMaxOn f s a` says `a` maximises `f` over `s`. The result is Mathlib's `IsCompact.exists_isMaxOn`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem exists_ismaxon :
    ∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : TopologicalSpace α] 
    [inst_2 : TopologicalSpace β] [ClosedIciTopology α] {s : Set β}, 
    IsCompact s → s.Nonempty → ∀ {f : β → α}, ContinuousOn f s → ∃ x ∈ s, IsMaxOn f s x := by sorry

end FamousTheorems
