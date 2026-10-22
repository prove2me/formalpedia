-- Prove2me | Theorems.Thm_CrossedProductGroups_Classification_corollary_3_5
-- name    : CrossedProductGroups.Classification.corollary_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:55.28599+00:00
-- url     : https://prove2.me/theorems/55c43c3a-bf9c-4fc7-9d50-1ea921657cc7
-- title:
--   Corollary 3.5, p. 20 — (η, ψ, γ) is an isomorphism of E2(H, G) iff η, γ are isomorphisms and (38), (39) hold for a unique t
-- statement:
--   Let $(\eta, \psi, \gamma) : (\alpha, f) \to (\alpha', f')$ be a morphism of $\mathcal{E}_2(H, G)$. It is an isomorphism in $\mathcal{E}_2(H, G)$ if and only if $\eta : H \to H$ and $\gamma : G \to G$ are group isomorphisms and there is a unique map $t : G \to H$ such that for all $h \in H$ and $g, g_1, g_2 \in G$
--   $$
--   \begin{aligned}
--   g \triangleright' h &= \eta\Big(t(g)\,\big(\gamma^{-1}(g) \triangleright \eta^{-1}(h)\big)\,t(g)^{-1}\Big), &(38)\\
--   f'(g_1, g_2) &= \eta\Big(t(g_1)\,\big(\gamma^{-1}(g_1) \triangleright t(g_2)\big)\, f\big(\gamma^{-1}(g_1), \gamma^{-1}(g_2)\big)\, t(g_1g_2)^{-1}\Big), &(39)
--   \end{aligned}
--   $$
--   and the isomorphism is
--   $$
--   \psi(h, g) = \Big(\eta\big(h\, t(\gamma(g))^{-1}\big),\; \gamma(g)\Big).
--   $$
--
--   Conditions (38) and (39) are the defining conditions of 2-equivalence (Definition 3.7), so this corollary identifies isomorphism in $\mathcal{E}_2(H, G)$ with $\approx_2$.
--
--   **Formalization Note.** The page says "there exists a unique map $t$ such that (38), (39) … Moreover, $\psi$ is given by the formula …". Conditions (38), (39) alone do not determine $t$ in general (for abelian $H$ with trivial action, $t$ can be multiplied by any group morphism $G \to H$), while the formula for $\psi$ does; so uniqueness is stated for $t$ satisfying (38), (39) and the formula together. "$\eta, \gamma$ are isomorphisms" is stated as the existence of `MulEquiv`s whose underlying homomorphisms are the components of the morphism.
-- source:
--   Agore & Militaru, Crossed product of groups. Applications, arXiv:0805.4077v2, p. 20, Corollary 3.5, (38), (39)

import Mathlib
import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem
import Definitions.Def_CrossedProductGroups_Classification_E2

namespace CrossedProductGroups.Classification

theorem corollary_3_5 {H G : Type*} [Group H] [Group G] (c c' : E2 H G) (m : c ⟶ c') :
    CategoryTheory.IsIso m ↔
      ∃ (η : H ≃* H) (γ : G ≃* G),
        η.toMonoidHom = (m : E2Hom c c').η ∧ γ.toMonoidHom = (m : E2Hom c c').γ ∧
        ∃! t : G → H,
          (∀ g : G, ∀ h : H,
            c'.1.1 g h = η (t g * c.1.1 (γ.symm g) (η.symm h) * (t g)⁻¹)) ∧
          (∀ g₁ g₂ : G, c'.1.2 g₁ g₂ =
            η (t g₁ * c.1.1 (γ.symm g₁) (t g₂) * c.1.2 (γ.symm g₁) (γ.symm g₂) *
              (t (g₁ * g₂))⁻¹)) ∧
          ∀ h : H, ∀ g : G, (m : E2Hom c c').ψ (h, g) = (η (h * (t (γ g))⁻¹), γ g) := by sorry

end CrossedProductGroups.Classification
