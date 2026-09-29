-- Prove2me | Theorems.Thm_FamousTheorems_exists_countable_union_perfect_of_isclosed
-- name    : FamousTheorems.exists_countable_union_perfect_of_isclosed
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:54:46.070977+00:00
-- url     : https://prove2.me/theorems/fd7e3432-beff-4470-985d-120c4ff31e2b
-- title:
--   The Cantor–Bendixson theorem
-- statement:
--   **The Cantor-Bendixson theorem.** Every closed subset of a Polish space splits as a countable set together with a perfect set. A closed set is therefore either countable or contains a perfect subset, and hence has cardinality either at most countable or exactly that of the continuum -- so the continuum hypothesis holds for closed sets, unconditionally. The perfect part is obtained by iterating the removal of isolated points through the ordinals, the process that gives the Cantor-Bendixson rank. This is the beginning of descriptive set theory. **Formalization note.** `Perfect` means closed with no isolated points, and the decomposition is a union. The result is Mathlib's `exists_countable_union_perfect_of_isClosed`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem exists_countable_union_perfect_of_isclosed :
    ∀ {α : Type u_1} [inst : TopologicalSpace α] {C : Set α} 
    [SecondCountableTopology α], IsClosed C → ∃ V D, V.Countable ∧ Perfect D ∧ C = V ∪ D := by sorry

end FamousTheorems
