-- Prove2me | Theorems.Thm_FamousTheorems_archimedean_field_embeds_reals_7b
-- name    : FamousTheorems.archimedean_field_embeds_reals_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:46.253323+00:00
-- url     : https://prove2.me/theorems/44b27668-f490-49fe-90ae-d1153c361094
-- title:
--   Every archimedean ordered field embeds in ℝ
-- statement:
--   **Every archimedean ordered field embeds in $\mathbb R$.** Let $\alpha$ be an archimedean linearly ordered field. Then there is an order-preserving ring homomorphism $\alpha\to\mathbb R$; since $\alpha$ is a field, it is injective.
--
--   Thus the archimedean ordered fields are exactly the subfields of $\mathbb R$ with the induced order, up to isomorphism, a result going back to Hölder. The embedding sends $x$ to the supremum of the rationals below $x$ in $\alpha$. With the uniqueness of the complete ordered field, it characterizes $\mathbb R$ as the largest archimedean ordered field.
--
--   **Formalization note.** Mathlib's `Real.nonemptyOrderRingHom`. `α →+*o ℝ` is the type of ordered ring homomorphisms, that is ring homomorphisms that are monotone. `IsStrictOrderedRing α` says that the order is compatible with the field operations.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.nonemptyOrderRingHom`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem archimedean_field_embeds_reals_7b (α : Type*) [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] : Nonempty (α →+*o ℝ) := by sorry

end FamousTheorems
