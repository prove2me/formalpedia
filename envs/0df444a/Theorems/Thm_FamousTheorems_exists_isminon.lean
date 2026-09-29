-- Prove2me | Theorems.Thm_FamousTheorems_exists_isminon
-- name    : FamousTheorems.exists_isminon
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:42.19189+00:00
-- url     : https://prove2.me/theorems/0e490cd0-c0fc-4ff8-9560-7444e4bdb150
-- title:
--   The extreme value theorem
-- statement:
--   **The extreme value theorem.** A continuous real-valued function on a nonempty compact set attains its minimum. Compactness is exactly the hypothesis that prevents the infimum from escaping: on an open or unbounded domain a continuous function may approach its infimum without reaching it. The theorem is the existence half of optimisation — it guarantees a minimiser exists before any method is applied to find one — and by applying it to $-f$ the maximum is attained too. The direct method in the calculus of variations is this argument run in an infinite-dimensional setting, with compactness replaced by weak compactness plus lower semicontinuity. **Formalization note.** `IsMinOn f s a` says `a` minimises `f` over `s`. The result is Mathlib's `IsCompact.exists_isMinOn`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem exists_isminon :
    ∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : TopologicalSpace α] 
    [inst_2 : TopologicalSpace β] [ClosedIicTopology α] {s : Set β}, 
    IsCompact s → s.Nonempty → ∀ {f : β → α}, ContinuousOn f s → ∃ x ∈ s, IsMinOn f s x := by sorry

end FamousTheorems
