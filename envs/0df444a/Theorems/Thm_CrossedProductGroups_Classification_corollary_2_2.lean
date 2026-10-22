-- Prove2me | Theorems.Thm_CrossedProductGroups_Classification_corollary_2_2
-- name    : CrossedProductGroups.Classification.corollary_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:38:59.052869+00:00
-- url     : https://prove2.me/theorems/8bab8a23-0e6f-4c5a-a231-9d0855eb67e5
-- title:
--   Corollary 2.2 (1)–(2), p. 13 — group morphisms out of and into a crossed product H #^f_α G
-- statement:
--   Let $X$ be a group and $(H, G, \alpha, f)$ a normalized crossed system.
--
--   1. A map $w : H \#_\alpha^f G \to X$ is a morphism of groups if and only if there are a group morphism $u : H \to X$ and a map $v : G \to X$ with
--   $$
--   v(g_1)v(g_2) = u(f(g_1, g_2))\,v(g_1g_2), \qquad v(g)u(h) = u(g \triangleright h)\,v(g), \qquad w(h, g) = u(h)v(g)
--   $$
--   for all $g, g_1, g_2 \in G$, $h \in H$ (conditions (20)–(22)).
--   2. A map $\psi : X \to H \#_\alpha^f G$ is a morphism of groups if and only if there are a map $u : X \to H$ and a group morphism $v : X \to G$ with
--   $$
--   u(xy) = u(x)\big(v(x) \triangleright u(y)\big) f\big(v(x), v(y)\big), \qquad \psi(x) = (u(x), v(x))
--   $$
--   for all $x, y \in X$ (conditions (23)–(24)).
--
--   These two descriptions are the working form of Theorem 2.1 and are the basis for computing all morphisms between two crossed products.
--
--   **Formalization Note.** Only items (1) and (2) of the corollary are formalized; items (3) and (4) (isomorphism criteria) are not used later in the paper's route to Theorem 3.8. A morphism of groups out of or into the crossed product is a map preserving the multiplication (8).
-- source:
--   Agore & Militaru, Crossed product of groups. Applications, arXiv:0805.4077v2, p. 13, Corollary 2.2 (1)–(2), (20)–(24)

import Mathlib
import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem

namespace CrossedProductGroups.Classification

theorem corollary_2_2 {H G : Type*} [Group H] [Group G] (α : G → MulAut H) (f : G → G → H)
    (hc : IsCrossedSystem α f) (hn : f 1 1 = 1) (X : Type*) [Group X] :
    (∀ w : H × G → X, (∀ x y : H × G, w (crossedMul α f x y) = w x * w y) ↔
      ∃ (u : H →* X) (v : G → X),
        (∀ g₁ g₂ : G, v g₁ * v g₂ = u (f g₁ g₂) * v (g₁ * g₂)) ∧
        (∀ g : G, ∀ h : H, v g * u h = u (α g h) * v g) ∧
        ∀ h : H, ∀ g : G, w (h, g) = u h * v g) ∧
    (∀ ψ : X → H × G, (∀ x y : X, ψ (x * y) = crossedMul α f (ψ x) (ψ y)) ↔
      ∃ (u : X → H) (v : X →* G),
        (∀ x y : X, u (x * y) = u x * α (v x) (u y) * f (v x) (v y)) ∧
        ∀ x : X, ψ x = (u x, v x)) := by sorry

end CrossedProductGroups.Classification
