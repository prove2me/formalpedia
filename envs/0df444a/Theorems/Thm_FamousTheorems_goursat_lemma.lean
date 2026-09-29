-- Prove2me | Theorems.Thm_FamousTheorems_goursat_lemma
-- name    : FamousTheorems.goursat_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:39.743814+00:00
-- url     : https://prove2.me/theorems/2302fe95-84d5-4a88-9856-09265b1c1511
-- title:
--   Goursat's lemma
-- statement:
--   **Goursat's lemma.** Let $G$ and $H$ be groups and $I\le G\times H$ a subgroup. Then there are subgroups $G'\le G$ and $H'\le H$, normal subgroups $M\trianglelefteq G'$ and $N\trianglelefteq H'$, and an isomorphism $e:G'/M\cong H'/N$, such that
--   $$I=\{(g,h)\in G'\times H' : e(gM)=hN\}.$$
--
--   So subgroups of a direct product correspond to isomorphisms between subquotients of the factors. The lemma is the standard tool for classifying subgroups of products and subdirect products. It is used in Galois theory to describe composita of fields and in the study of images of Galois representations.
--
--   **Formalization note.** Mathlib's `Subgroup.goursat`. The subgroup is written as the image under the inclusion $G'\times H'\to G\times H$ of the preimage of the graph of `e` under the quotient map $G'\times H'\to G'/M\times H'/N$. The normality of `M` and `N` is supplied inside the existential.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Subgroup.goursat`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem goursat_lemma {G H : Type*} [Group G] [Group H] (I : Subgroup (G × H)) :
    ∃ (G' : Subgroup G) (H' : Subgroup H) (M : Subgroup G') (N : Subgroup H') (_ : M.Normal)
      (_ : N.Normal) (e : G' ⧸ M ≃* H' ⧸ N),
      I = (e.toMonoidHom.graph.comap ((QuotientGroup.mk' M).prodMap (QuotientGroup.mk' N))).map
        (G'.subtype.prodMap H'.subtype) := by sorry

end FamousTheorems
