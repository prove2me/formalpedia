-- Prove2me | Theorems.Thm_CrossedProductGroups_Classification_iso_iff_equiv2
-- name    : CrossedProductGroups.Classification.iso_iff_equiv2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:07.687115+00:00
-- url     : https://prove2.me/theorems/d9e77ce5-a09d-403d-a764-a25e9f54bcb0
-- title:
--   §3, p. 21 — normalized crossed systems are 2-equivalent iff isomorphic in E2(H, G); ≈2 is an equivalence relation
-- statement:
--   Let $H$ and $G$ be groups. For normalized crossed systems $(\alpha, f), (\alpha', f') \in \mathrm{Crossed}(H, G)$,
--   $$
--   (H, G, \alpha, f) \approx_2 (H, G, \alpha', f') \iff (\alpha, f) \cong (\alpha', f') \text{ in } \mathcal{E}_2(H, G),
--   $$
--   and $\approx_2$ is an equivalence relation on $\mathrm{Crossed}(H, G)$.
--
--   This is the bridge between the explicit relation of Definition 3.7 and the categorical notion of isomorphism; it is the content of the paragraph following Definition 3.7.
--
--   **Formalization Note.** The source states this as an unnumbered consequence of Corollary 3.5 (p. 21). Isomorphism in $\mathcal{E}_2(H, G)$ is `Nonempty (c ≅ c')` for the category instance on `E2 H G`.
-- source:
--   Agore & Militaru, Crossed product of groups. Applications, arXiv:0805.4077v2, p. 21, §3, paragraph after Definition 3.7

import Mathlib
import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem
import Definitions.Def_CrossedProductGroups_Classification_E2

namespace CrossedProductGroups.Classification

theorem iso_iff_equiv2 (H G : Type*) [Group H] [Group G] :
    (∀ c c' : E2 H G, Nonempty (c ≅ c') ↔ Equiv2 c c') ∧
      Equivalence (Equiv2 (H := H) (G := G)) := by sorry

end CrossedProductGroups.Classification
