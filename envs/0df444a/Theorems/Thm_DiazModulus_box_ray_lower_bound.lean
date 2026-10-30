-- Prove2me | Theorems.Thm_DiazModulus_box_ray_lower_bound
-- name    : DiazModulus.box_ray_lower_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:20.164248+00:00
-- url     : https://prove2.me/theorems/9b192530-242a-417d-8ef9-1d4b8db171fe
-- title:
--   Partial box count along a ray: $u^{|H|+|J|} D_0^{|H|} D_1^{|J|} \le (uD_0+1)^{|H|} (2uD_1+1)^{|J|}$
-- statement:
--   Let $H$ and $J$ be finite sets (of elements of arbitrary types) and $D_0, D_1, u \in \mathbb{N}$. Then $u^{|H|+|J|} D_0^{|H|} D_1^{|J|} \le (uD_0 + 1)^{|H|} (2uD_1 + 1)^{|J|}$ (the right side is written in Lean as a product of constant factors over $H$ and over $J$). No hypothesis is needed.
--
--   **Proof.** The left side is $(uD_0)^{|H|} (uD_1)^{|J|}$, and $uD_0 \le uD_0 + 1$, $uD_1 \le 2uD_1 + 1$; take powers and multiply.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Elementary. A partial count of the box (uD₀; uD₁), compare M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 5.7 (§5.3.1, p. 159; Chapter 5 is by D. Roy). C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem box_ray_lower_bound {A₀ A₁ : Type*} (D₀ D₁ : ℕ) (H : Finset A₀) (J : Finset A₁) (u : ℕ) :
    u ^ (H.card + J.card) * (D₀ ^ H.card * D₁ ^ J.card)
      ≤ (∏ _h ∈ H, (u * D₀ + 1)) * ∏ _j ∈ J, (2 * (u * D₁) + 1) := by
  sorry

end DiazModulus
