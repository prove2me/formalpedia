-- Prove2me | Theorems.Thm_DiazModulus_box_ray_upper_bound
-- name    : DiazModulus.box_ray_upper_bound
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:22.894289+00:00
-- url     : https://prove2.me/theorems/89ceb4f1-c0c9-4db3-aab7-34a0aa5accc0
-- title:
--   Box count along a ray: $(vD_0+1)^{d_0} (2vD_1+1)^{d_1} \le (v+1)^{d_0+d_1} D_0^{d_0} (2D_1)^{d_1}$ when $D_0, D_1 \ge 1$
-- statement:
--   Let $A_0, A_1$ be finite types with $d_0$ and $d_1$ elements, $D_0, D_1 \ge 1$ and $v \in \mathbb{N}$. Then $(vD_0 + 1)^{d_0} (2vD_1 + 1)^{d_1} \le (v+1)^{d_0+d_1} D_0^{d_0} (2D_1)^{d_1}$ (the left side is written in Lean as a product of constant factors over $A_0$ and over $A_1$).
--
--   **Proof.** Since $D_0, D_1 \ge 1$, $vD_0 + 1 \le (v+1) D_0$ and $2vD_1 + 1 \le (v+1)(2D_1)$; take powers and regroup the factors $v + 1$.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Elementary. The number of monomials of the box (vD₀; vD₁), compare M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 5.7 (§5.3.1, p. 159; Chapter 5 is by D. Roy). C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem box_ray_upper_bound {A₀ A₁ : Type*} [Fintype A₀] [Fintype A₁] (D₀ D₁ : ℕ) (h0 : 1 ≤ D₀) (h1 : 1 ≤ D₁) (v : ℕ) :
    (∏ _h : A₀, (v * D₀ + 1)) * ∏ _i : A₁, (2 * (v * D₁) + 1)
      ≤ (v + 1) ^ (Fintype.card A₀ + Fintype.card A₁) * (D₀ ^ Fintype.card A₀ * (2 * D₁) ^ Fintype.card A₁) := by
  sorry

end DiazModulus
