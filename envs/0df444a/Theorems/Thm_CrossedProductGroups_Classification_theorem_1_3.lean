-- Prove2me | Theorems.Thm_CrossedProductGroups_Classification_theorem_1_3
-- name    : CrossedProductGroups.Classification.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:38:58.724183+00:00
-- url     : https://prove2.me/theorems/f0639945-e9fa-40b7-a861-7ea12a7b16f9
-- title:
--   Theorem 1.3, p. 4 — (8) is associative iff (H, G, α, f) is a crossed system; then H #^f_α G is a group with unit (f(1, 1)⁻¹, 1)
-- statement:
--   Let $H$ and $G$ be groups and let $\alpha : G \to \mathrm{Aut}(H)$ and $f : G \times G \to H$ be arbitrary maps. Equip $H \times G$ with the multiplication
--   $$
--   (h_1, g_1) \cdot (h_2, g_2) = \big(h_1\,(g_1 \triangleright h_2)\, f(g_1, g_2),\; g_1g_2\big).
--   $$
--   Then:
--
--   1. this multiplication is associative if and only if $(H, G, \alpha, f)$ is a crossed system;
--   2. in that case $(H \times G, \cdot)$ is a group with identity element $\big(f(1,1)^{-1}, 1\big)$: this element is a two-sided unit, and every element has a two-sided inverse.
--
--   The group so obtained is the crossed product $H \#_\alpha^f G$. The theorem says that the cocycle conditions of Definition 1.1 are exactly what is needed for (8) to define a group.
--
--   **Formalization Note.** The crossed system is not assumed normalized. "Is a group with unit $u$" is stated as associativity together with the two-sided unit and two-sided inverse properties of $u = (f(1,1)^{-1}, 1)$ for the operation `crossedMul α f`.
-- source:
--   Agore & Militaru, Crossed product of groups. Applications, arXiv:0805.4077v2, p. 4, Theorem 1.3

import Mathlib
import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem

namespace CrossedProductGroups.Classification

theorem theorem_1_3 {H G : Type*} [Group H] [Group G] (α : G → MulAut H) (f : G → G → H) :
    ((∀ x y z : H × G,
        crossedMul α f (crossedMul α f x y) z = crossedMul α f x (crossedMul α f y z)) ↔
      IsCrossedSystem α f) ∧
    (IsCrossedSystem α f →
      (∀ x : H × G, crossedMul α f ((f 1 1)⁻¹, 1) x = x ∧ crossedMul α f x ((f 1 1)⁻¹, 1) = x) ∧
      ∀ x : H × G, ∃ y : H × G,
        crossedMul α f y x = ((f 1 1)⁻¹, 1) ∧ crossedMul α f x y = ((f 1 1)⁻¹, 1)) := by sorry

end CrossedProductGroups.Classification
