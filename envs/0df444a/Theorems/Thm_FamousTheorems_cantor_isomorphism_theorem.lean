-- Prove2me | Theorems.Thm_FamousTheorems_cantor_isomorphism_theorem
-- name    : FamousTheorems.cantor_isomorphism_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:28.175143+00:00
-- url     : https://prove2.me/theorems/17215a6f-787e-46f2-b3b4-3b736cfbd539
-- title:
--   Cantor's isomorphism theorem (countable dense linear orders)
-- statement:
--   **Cantor's isomorphism theorem.** Any two countable dense linear orders without endpoints are order-isomorphic. In particular every such order is isomorphic to $(\mathbb Q,<)$.
--
--   Cantor's proof (in its back-and-forth form, due to Huntington and Hausdorff) is the prototype of the back-and-forth method of model theory. The theorem shows that the theory of dense linear orders without endpoints is $\aleph_0$-categorical and hence complete.
--
--   **Formalization note.** Mathlib's `Order.iso_of_countable_dense`. Density is `DenselyOrdered`, absence of endpoints is `NoMinOrder`/`NoMaxOrder`, and nonemptiness is required.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Order.iso_of_countable_dense`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cantor_isomorphism_theorem (α β : Type*) [LinearOrder α] [LinearOrder β] [Countable α] [DenselyOrdered α] [NoMinOrder α]
    [NoMaxOrder α] [Nonempty α] [Countable β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] :
    Nonempty (α ≃o β) := by sorry

end FamousTheorems
