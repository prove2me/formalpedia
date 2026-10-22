-- Prove2me | Theorems.Thm_CrossedProductGroups_Classification_lemma_1_2
-- name    : CrossedProductGroups.Classification.lemma_1_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:38:55.15697+00:00
-- url     : https://prove2.me/theorems/a887697a-a79d-41bd-b6ca-09efc94061ef
-- title:
--   Lemma 1.2, p. 4 — f(g, 1) = g ⊲ f(1, 1), 1 ⊲ h = f(1, 1) h f(1, 1)⁻¹, f(1, g) = f(1, 1) in a crossed system
-- statement:
--   Let $(H, G, \alpha, f)$ be a crossed system, with $g \triangleright h = \alpha(g)(h)$. Then for every $g \in G$ and $h \in H$
--   $$
--   f(g, 1) = g \triangleright f(1, 1), \qquad 1 \triangleright h = f(1, 1)\, h\, f(1, 1)^{-1}, \qquad f(1, g) = f(1, 1).
--   $$
--   In particular, if the crossed system is normalized ($f(1,1) = 1$), then $f(1, g) = f(g, 1) = 1$ and $1 \triangleright h = h$ for all $g \in G$, $h \in H$.
--
--   These identities control the behaviour of a crossed system at the identity of $G$; they are used repeatedly, e.g. to show that $(h, 1)$ and $(1, g)$ generate the crossed product.
-- source:
--   Agore & Militaru, Crossed product of groups. Applications, arXiv:0805.4077v2, p. 4, Lemma 1.2, (4)–(7)

import Mathlib
import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem

namespace CrossedProductGroups.Classification

theorem lemma_1_2 {H G : Type*} [Group H] [Group G] (α : G → MulAut H) (f : G → G → H)
    (hc : IsCrossedSystem α f) :
    (∀ g : G, f g 1 = α g (f 1 1)) ∧
    (∀ h : H, α 1 h = f 1 1 * h * (f 1 1)⁻¹) ∧
    (∀ g : G, f 1 g = f 1 1) ∧
    (f 1 1 = 1 → (∀ g : G, f 1 g = 1 ∧ f g 1 = 1) ∧ ∀ h : H, α 1 h = h) := by sorry

end CrossedProductGroups.Classification
