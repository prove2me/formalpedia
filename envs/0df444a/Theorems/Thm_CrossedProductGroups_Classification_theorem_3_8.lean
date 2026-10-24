-- Prove2me | Theorems.Thm_CrossedProductGroups_Classification_theorem_3_8
-- name    : CrossedProductGroups.Classification.theorem_3_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:57.404736+00:00
-- url     : https://prove2.me/theorems/dee78eeb-e515-4479-9e4a-5102723e7860
-- title:
--   Theorem 3.8, p. 21 — the skeleton of E2(H, G) is in bijection with Crossed(H, G)/≈2
-- statement:
--   Let $H$ and $G$ be groups. Then $\approx_2$ is an equivalence relation on $\mathrm{Crossed}(H, G)$, and there is a bijection
--   $$
--   \mathrm{Ob}\big(\mathrm{Sk}\,\mathcal{E}_2(H, G)\big) \;\cong\; \mathrm{Crossed}(H, G)/\!\approx_2
--   $$
--   between the objects of the skeleton of the category $\mathcal{E}_2(H, G)$ and the quotient set, which sends the isomorphism class of a normalized crossed system $(\alpha, f)$ to its $\approx_2$-class.
--
--   This is a general Schreier-type classification theorem: the crossed products $H \#_\alpha^f G$, up to isomorphisms compatible with $H$ and $G$ through arbitrary automorphisms $\eta$ and $\gamma$, are classified by the explicit relation $\approx_2$ on the data $(\alpha, f)$.
--
--   **Formalization Note.** The skeleton is Mathlib's `CategoryTheory.Skeleton (E2 H G)`, whose elements are isomorphism classes of objects. The statement includes `Equivalence Equiv2` (asserted in the sentence before the theorem on p. 21), so `Quot Equiv2` is the honest quotient set. The bijection is required to send `toSkeleton c` to the class of `c`, as in the paper's proof via Corollary 3.5; without this clause the statement would only compare cardinalities.
-- source:
--   Agore & Militaru, Crossed product of groups. Applications, arXiv:0805.4077v2, p. 21, Theorem 3.8 and the preceding paragraph

import Mathlib
import Definitions.Def_CrossedProductGroups_Classification_CrossedSystem
import Definitions.Def_CrossedProductGroups_Classification_E2

namespace CrossedProductGroups.Classification

theorem theorem_3_8 (H G : Type*) [Group H] [Group G] :
    Equivalence (Equiv2 (H := H) (G := G)) ∧
      ∃ e : CategoryTheory.Skeleton (E2 H G) ≃ Quot (Equiv2 (H := H) (G := G)),
        ∀ c : Crossed H G,
          e (CategoryTheory.toSkeleton (C := E2 H G) c) = Quot.mk _ c := by sorry

end CrossedProductGroups.Classification
