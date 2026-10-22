-- Prove2me | Theorems.Thm_CrossedProductGroups_Classification_proposition_3_4
-- name    : CrossedProductGroups.Classification.proposition_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:49.420851+00:00
-- url     : https://prove2.me/theorems/4e88fd8f-a016-49dd-9450-f2802e4e1e65
-- title:
--   Proposition 3.4, p. 20 — (η, ψ, γ) is a morphism of E2(H, G) iff there is a unique r : G → H with (35)–(37)
-- statement:
--   Let $(\alpha, f)$ and $(\alpha', f')$ be normalized crossed systems, $\eta : H \to H$ and $\gamma : G \to G$ group morphisms, and $\psi : H \times G \to H \times G$ a map. Then $(\eta, \psi, \gamma)$ is a morphism $(\alpha, f) \to (\alpha', f')$ of $\mathcal{E}_2(H, G)$ if and only if there is a unique map $r : G \to H$ such that for all $h \in H$ and $g, g_1, g_2 \in G$
--   $$
--   \begin{aligned}
--   \eta(g \triangleright h)\, r(g) &= r(g)\,\big(\gamma(g) \triangleright' \eta(h)\big), &(35)\\
--   r(g_1)\,\big(\gamma(g_1) \triangleright' r(g_2)\big)\, f'\big(\gamma(g_1), \gamma(g_2)\big) &= \eta\big(f(g_1, g_2)\big)\, r(g_1g_2), &(36)\\
--   \psi(h, g) &= \big(\eta(h)\, r(g),\; \gamma(g)\big). &(37)
--   \end{aligned}
--   $$
--
--   This parametrizes the morphisms of $\mathcal{E}_2(H, G)$ with fixed outer components $\eta, \gamma$ by maps $r$ subject to two conditions.
--
--   **Formalization Note.** The paper's "η, γ are morphisms of groups" is carried by their types (`H →* H`, `G →* G`), since they are components of the triple. "$(\eta, \psi, \gamma)$ is a morphism of $\mathcal{E}_2(H, G)$" is stated as the existence of an `E2Hom c c'` with these three components.
-- source:
--   Agore & Militaru, Crossed product of groups. Applications, arXiv:0805.4077v2, p. 20, Proposition 3.4, (35)–(37)

import Mathlib
import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem
import Definitions.Def_CrossedProductGroups_Classification_E2

namespace CrossedProductGroups.Classification

theorem proposition_3_4 {H G : Type*} [Group H] [Group G] (c c' : E2 H G)
    (η : H →* H) (γ : G →* G) (ψ : H × G → H × G) :
    (∃ m : E2Hom c c', m.η = η ∧ m.γ = γ ∧ m.ψ = ψ) ↔
      ∃! r : G → H,
        (∀ g : G, ∀ h : H, η (c.1.1 g h) * r g = r g * c'.1.1 (γ g) (η h)) ∧
        (∀ g₁ g₂ : G, r g₁ * c'.1.1 (γ g₁) (r g₂) * c'.1.2 (γ g₁) (γ g₂) =
          η (c.1.2 g₁ g₂) * r (g₁ * g₂)) ∧
        ∀ h : H, ∀ g : G, ψ (h, g) = (η h * r g, γ g) := by sorry

end CrossedProductGroups.Classification
