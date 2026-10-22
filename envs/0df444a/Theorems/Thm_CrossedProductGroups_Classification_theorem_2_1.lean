-- Prove2me | Theorems.Thm_CrossedProductGroups_Classification_theorem_2_1
-- name    : CrossedProductGroups.Classification.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:06.501982+00:00
-- url     : https://prove2.me/theorems/744371b3-11d2-4036-b54d-63d1dbee91c6
-- title:
--   Theorem 2.1, p. 11 — the crossed product is an initial object of ΓC and a final object of CΓ
-- statement:
--   Let $(H, G, \alpha, f)$ be a normalized crossed system and $X$ a group. Write $i_H(h) = (h, 1)$, $i_G(g) = (1, g)$, $\pi_H(h, g) = h$ and $\pi_G(h, g) = g$.
--
--   1. **Initial object.** $(H \#_\alpha^f G, (i_H, i_G))$ is an object of the category ${}_\Gamma\mathcal{C}$: $i_H$ is a group morphism and $v(g_1)v(g_2) = u(f(g_1, g_2))v(g_1g_2)$, $v(g)u(h) = u(g \triangleright h)v(g)$ (18) hold for $u = i_H$, $v = i_G$. Moreover, for every group morphism $u : H \to X$ and every map $v : G \to X$ satisfying (18), there is a unique group morphism $w : H \#_\alpha^f G \to X$ with $w \circ i_H = u$ and $w \circ i_G = v$.
--   2. **Final object.** $(H \#_\alpha^f G, (\pi_H, \pi_G))$ is an object of $\mathcal{C}_\Gamma$: $\pi_G$ is a group morphism and
--   $$
--   u(xy) = u(x)\big(v(x) \triangleright u(y)\big) f\big(v(x), v(y)\big) \tag{19}
--   $$
--   holds for $u = \pi_H$, $v = \pi_G$. Moreover, for every group morphism $v : X \to G$ and every map $u : X \to H$ satisfying (19), there is a unique group morphism $w : X \to H \#_\alpha^f G$ with $\pi_H \circ w = u$ and $\pi_G \circ w = v$.
--
--   So the crossed product is characterized by two universal properties of different nature, one for maps out of it and one for maps into it.
--
--   **Formalization Note.** The categories ${}_\Gamma\mathcal{C}$ and $\mathcal{C}_\Gamma$ are not built; "initial" and "final" are unfolded into existence and uniqueness of the morphism to (from) every object, and the claims "it can be checked that … is an object" (p. 11) are included. A group morphism out of or into the crossed product is a map preserving the multiplication (8); the group $X$ is a universally quantified parameter of the theorem.
-- source:
--   Agore & Militaru, Crossed product of groups. Applications, arXiv:0805.4077v2, p. 11, Theorem 2.1, with (18), (19) and the categories ΓC, CΓ defined on p. 11

import Mathlib
import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem

namespace CrossedProductGroups.Classification

theorem theorem_2_1 {H G : Type*} [Group H] [Group G] (α : G → MulAut H) (f : G → G → H)
    (hc : IsCrossedSystem α f) (hn : f 1 1 = 1) (X : Type*) [Group X] :
    -- (1) `(H #^f_α G, (i_H, i_G))` is an object of `_ΓC` ...
    ((∀ h₁ h₂ : H, crossedMul α f (h₁, 1) (h₂, 1) = (h₁ * h₂, 1)) ∧
      (∀ g₁ g₂ : G, crossedMul α f (1, g₁) (1, g₂) = crossedMul α f (f g₁ g₂, 1) (1, g₁ * g₂)) ∧
      (∀ g : G, ∀ h : H, crossedMul α f (1, g) (h, 1) = crossedMul α f (α g h, 1) (1, g))) ∧
    -- ... and it is initial: a unique morphism to every object `(X, (u, v))` of `_ΓC`
    (∀ (u : H →* X) (v : G → X),
      (∀ g₁ g₂ : G, v g₁ * v g₂ = u (f g₁ g₂) * v (g₁ * g₂)) →
      (∀ g : G, ∀ h : H, v g * u h = u (α g h) * v g) →
      ∃! w : H × G → X, (∀ x y : H × G, w (crossedMul α f x y) = w x * w y) ∧
        (∀ h : H, w (h, 1) = u h) ∧ ∀ g : G, w (1, g) = v g) ∧
    -- (2) `(H #^f_α G, (π_H, π_G))` is an object of `C_Γ` ...
    ((∀ x y : H × G, (crossedMul α f x y).2 = x.2 * y.2) ∧
      (∀ x y : H × G, (crossedMul α f x y).1 = x.1 * α x.2 y.1 * f x.2 y.2)) ∧
    -- ... and it is final: a unique morphism from every object `(X, (u, v))` of `C_Γ`
    (∀ (v : X →* G) (u : X → H),
      (∀ x y : X, u (x * y) = u x * α (v x) (u y) * f (v x) (v y)) →
      ∃! w : X → H × G, (∀ x y : X, w (x * y) = crossedMul α f (w x) (w y)) ∧
        (∀ x : X, (w x).1 = u x) ∧ ∀ x : X, (w x).2 = v x) := by sorry

end CrossedProductGroups.Classification
