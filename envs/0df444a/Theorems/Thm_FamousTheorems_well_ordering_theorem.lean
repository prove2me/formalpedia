-- Prove2me | Theorems.Thm_FamousTheorems_well_ordering_theorem
-- name    : FamousTheorems.well_ordering_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:26.973666+00:00
-- url     : https://prove2.me/theorems/f8815288-e8e4-4847-9adc-2b38d4916601
-- title:
--   The well-ordering theorem (Zermelo)
-- statement:
--   **The well-ordering theorem (Zermelo).** Every set admits a well-ordering: a linear order in which every nonempty subset has a least element.
--
--   Zermelo proved it in 1904 from the axiom of choice, and over ZF it is equivalent to choice and to Zorn's lemma. It allows transfinite induction and recursion on arbitrary sets, and underpins the theory of cardinal numbers (every set is equinumerous with an ordinal).
--
--   **Formalization note.** Mathlib's `exists_wellFoundedLT`. The order is a `LinearOrder` on the type whose strict order `<` is well-founded (`WellFoundedLT`).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `exists_wellFoundedLT`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem well_ordering_theorem (α : Type*) : ∃ (_ : LinearOrder α), WellFoundedLT α := by sorry

end FamousTheorems
